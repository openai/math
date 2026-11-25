import OAI.Optimization.LinearProgramming.PrimalDual.CallSegmentsFirst
import OAI.Optimization.LinearProgramming.PrimalDual.CallSegmentsJoint

/-! The original and optional joint feasibility invocations are contiguous segments of
the same bounded, normal-entry trace that produces the optimization answer. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace CallSegments

open RAM RAM.Call RAM.Tape RAM.Block Polynomial Bridge

/-- A complete physical trace, its consecutive program pieces, and its uniform
time and scalar bounds. The three routes record exactly one, two, and two calls. -/
def Report (p : Program) (C E bC bE : ℕ) {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) (c : Fin d → ℚ) : Prop :=
  let host := program p C E
  let input := lpInput A b++List.ofFn c
  let initial := start [m,d] input
  let L := totalBits input
  let height := decoderLimit d ((calleeBitsPolynomial bC bE).eval L)
  let T := time p C E
  let U := optimizationBitsPolynomial bC bE
  ∃ (answer : Answer) (k : ℕ) (tr : Fin (k+1) → State ℚ),
    Trace host initial k tr ∧ Joined host p height (itinerary p C E A b c answer) initial k (tr (Fin.last k)) ∧
    (∀ other, Trace host initial k other → other = tr) ∧
    count (itinerary p C E A b c answer) = answer.calls ∧ answer.calls ≤ 2 ∧
    k ≤ polyBound (T.eval 1) T.natDegree (m+d) ∧
    (∀ i, scalarBound (polyBound (U.eval 1) U.natDegree L) (tr i)) ∧
    (tr (Fin.last k)).output = some answer.tag ∧ OptimizationOutput A b c (tr (Fin.last k))

private theorem report_of_joined (p : Program) (C E bC bE : ℕ) {m d k : ℕ}
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ) (answer : Answer) (z : State ℚ)
    (joined : Joined (program p C E) p (decoderLimit d ((calleeBitsPolynomial bC bE).eval
      (totalBits (lpInput A b++List.ofFn c)))) (itinerary p C E A b c answer)
      (start [m,d] (lpInput A b++List.ofFn c)) k z)
    (budget : k ≤ (time p C E).eval (m+d)) (tag : z.output = some answer.tag) (out : OptimizationOutput A b c z) :
    Report p C E bC bE A b c := by
  let U := optimizationBitsPolynomial bC bE
  let L := totalBits (lpInput A b++List.ofFn c)
  have dim : d ≤ L := (Nat.le_add_left d m).trans (dimensions_le_optInputBits A b c)
  have height := (optimization_scalar_bound bC bE d L dim).trans (polynomial_eval_le_polyBound U L)
  obtain ⟨tr,valid,last,safe⟩ := joined.execution.to_trace
  refine ⟨answer,k,tr,valid,?_,fun _ other => unique_trace other valid,count_itinerary p C E A b c answer,
    answer.calls_le_two,budget.trans (polynomial_eval_le_polyBound _ _),fun i j => (safe i j).trans height,?_,?_⟩
  · rwa [last]
  · rwa [last]
  · rwa [last]

/-- Given the actual uniform feasibility ROM and its bounds, this is the fixed
Corollary 1.2 optimizer with a one- or two-call transcript on its own final run. -/
theorem optimizer_trace_segments (p : Program) (C E bC bE : ℕ) (solve : BoundedSolver p C E bC bE)
    {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) (c : Fin d → ℚ) : Report p C E bC bE A b c := by
  let L := totalBits (lpInput A b++List.ofFn c)
  let H := (calleeBitsPolynomial bC bE).eval L
  let G := decoderLimit d H
  let B := firstLimit p C E m d
  let off := firstReturnBase p C E
  let window := firstWindowPolynomial p C E
  let secondBudget := oraclePolynomial C E
  have wide : H ≤ G := (decoderLimit_bounds d H).1
  have hB : B ≤ window.eval (m+d) := firstWindow_bound p C E m d
  have places := EndBlocks.placed (bs:=endingBlocks) (withFirstCall_locations p C E firstReturn (endingCode p)).2.2
  obtain ⟨zero,_,safeStart,firstBits,jointBits⟩ := callee_bits A b c bC bE
  obtain ⟨k,tr,guest,hk,small,valid⟩ := solve m d hm hd A b
  let last := tr (Fin.last k)
  obtain ⟨tag,tagged⟩ : ∃ tag, last.output = some tag := valid.elim (fun v => ⟨0,v.1⟩) (fun v => ⟨1,v.1⟩)
  obtain ⟨n,hn,s,front,safe,frame⟩ := first_parts p C E A b c zero wide safeStart tr guest hk
    (fun i j => (small i j).trans firstBits) valid tagged
  have firstBound := hn.trans (firstTime_bound p C E m d k hk)
  have total {l r : ℕ} (cap : l ≤ endingCost m d B r) (oracle : r ≤ secondBudget.eval (m+d)) :
      n+l ≤ (time p C E).eval (m+d) := by
    simpa only [time,Polynomial.eval_add] using Nat.add_le_add firstBound
      (cap.trans (endingCost_le window secondBudget m d B r hB oracle))
  rcases valid with ⟨feasibleTag,feasible⟩ | ⟨certificateTag,certificate⟩
  · have t0 : tag = 0 := Option.some.inj (tagged.symm.trans feasibleTag)
    subst tag
    obtain ⟨j,u,second,hj,small₂,answer⟩ := solve (rowCount m d) (d+m) (by unfold rowCount; omega)
      (by omega) (finJointMatrix A b c) (finJointRhs b c)
    let jointLast := u (Fin.last j)
    obtain ⟨tag,ret⟩ : ∃ tag, jointLast.output = some tag := answer.elim (fun v => ⟨0,v.1⟩) (fun v => ⟨1,v.1⟩)
    obtain ⟨l,hl,w,joint,ws,read⟩ := joint_parts p C E A b c last s zero wide safe frame u second
      (fun i a => (small₂ i a).trans jointBits) answer ret
    have jointBound : j ≤ secondBudget.eval (m+d) := hj.trans_eq (joint_time_eval _ _ _ _)
    have charge {q : ℕ} (cost : q ≤ returnBudget.eval (m+d)) : n+(l+(q+1)) ≤ (time p C E).eval (m+d) := by
      apply total (r:=j) _ jointBound
      have charged : l ≤ stageBudget.eval (m+d+B)+secondCallCost m d B j := hl
      unfold endingCost
      unfold secondCallCost at charged
      omega
    rcases answer with ⟨h0,good⟩ | ⟨h1,bad⟩
    · have t0 : tag = 0 := Option.some.inj (ret.symm.trans h0)
      subst tag
      obtain ⟨t,q,decode,hq,output⟩ := secondOptimum_correct A b c jointLast good w ws read.rows read.cols
        (fun i _ => read.guest i) read.objective
      have term := Joined.single (Realizes.terminal (guest:=p) places.optimum decode)
      apply report_of_joined p C E bC bE A b c .optimum _ (front.append (joint.append term))
        (charge (by simpa [returnBudget] using hq)) rfl
      exact (optimizationOutput_congr (t:={t.atPC 0 with output:=some 1}) rfl rfl).2 output
    · have t1 : tag = 1 := Option.some.inj (ret.symm.trans h1)
      subst tag
      obtain ⟨t,q,decode,hq,output⟩ := secondRay_correct A b c (readVector last 0 d) feasible jointLast bad w ws
        read.rows read.cols read.guest read.objective read.point
      have term := Joined.single (Realizes.terminal (guest:=p) places.ray decode)
      apply report_of_joined p C E bC bE A b c .ray _ (front.append (joint.append term)) (charge hq) rfl
      exact (optimizationOutput_congr (t:={t.atPC 0 with output:=some 2}) rfl rfl).2 output
  · have t1 : tag = 1 := Option.some.inj (tagged.symm.trans certificateTag)
    subst tag
    obtain ⟨t,q,decode,hq,output⟩ := firstCertificate_correct A b c last certificate s safe frame.rows frame.cols frame.result
    have term := Joined.single (Realizes.terminal (guest:=p) places.first (widenBlock decode wide))
    apply report_of_joined p C E bC bE A b c .certificate _ (front.append term)
      (total (r:=0) (by unfold endingCost; omega) (Nat.zero_le _)) rfl
    exact (optimizationOutput_congr (t:={t.atPC 0 with output:=some 0}) rfl rfl).2 output

/-- The feasibility program and all of its uniform bounds are selected before
the optimization input, as in the principal strong-polynomiality contract. -/
theorem optimizer_trace_segments_of_feasibility (h : StronglyPolynomialFeasibility) :
    ∃ (p : Program) (C E bC bE : ℕ), BoundedSolver p C E bC bE ∧
      ∀ {m d : ℕ}, 0 < m → 0 < d → ∀ (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ),
        Report p C E bC bE A b c := by
  obtain ⟨p,C,E,bC,bE,solve⟩ := h
  exact ⟨p,C,E,bC,bE,solve,fun {m d} hm hd A b c => optimizer_trace_segments p C E bC bE solve hm hd A b c⟩

end CallSegments
end PrimalDual
end LinearProgramming
end Optimization
end OAI
