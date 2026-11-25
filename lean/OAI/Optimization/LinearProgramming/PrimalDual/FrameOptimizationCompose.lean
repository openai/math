import OAI.Optimization.LinearProgramming.RAM.FrameFirstBounds
import OAI.Optimization.LinearProgramming.PrimalDual.FrameOptimizationBits
import OAI.Optimization.LinearProgramming.PrimalDual.EndingCost
import OAI.Optimization.LinearProgramming.RAM.EvalWeaken

/-! Corollary 1.2: a fixed strongly polynomial certificate-producing LP optimizer obtained
from any ordinary certificate-producing strongly polynomial feasibility program. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM RAM.Call RAM.Tape RAM.Block Polynomial Bridge

/-- Correct callback for each of the two possible return tags of the first call. -/
structure VerifiedEnding (firstReturn : Nat → Nat → Nat) (endingCode : Program → Nat → Program) : Prop where
  certificate {m d H B pc : Nat} {target original : Program}
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ) (first : State ℚ)
    (cert : Certificate A b (readVector first 0 m)) (s : Memory ℚ)
    (safe : Good (fun q => ratBits q ≤ H) s) (hm : s.index 9=m) (hd : s.index 11=d)
    (even : ∀ i, s.data (2*i)=first.data i) (placed : CodeAt target pc (endingCode original pc)) :
    ∃ n ≤ endingCost m d B 0, ∃ z, Execution target (scalarBound (decoderLimit d H))
      (s.atPC (firstReturn pc 1)) n z ∧ OptimizationOutput A b c z
  feasible {m d H B pc k : Nat} {target original : Program}
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c x₀ : Fin d → ℚ) (hx₀ : Feasible A b x₀)
    (s : Memory ℚ) (safe : Good (fun q => ratBits q ≤ H) s) (hz : 3 ≤ H)
    (hm : s.index 9=m) (hd : s.index 11=d) (hB : s.index 21=B)
    (saved : ∀ i < origLen m d, s.data (3+2*i)=optInputWord A b c i)
    (guest : ∀ i : Fin d, s.data (2*i.val)=x₀ i)
    (dataTail : ∀ i, B+2 ≤ i → s.data (2*i)=0) (indexTail : ∀ i, B+2 ≤ i → s.index (2*i)=0)
    (tr : Fin (k+1) → State ℚ)
    (oracle : Trace original (start [rowCount m d,d+m] (lpInput (finJointMatrix A b c) (finJointRhs b c))) k tr)
    (oracleSafe : ∀ i, scalarBound H (tr i))
    (answer : FeasibilityOutput (finJointMatrix A b c) (finJointRhs b c) (tr (Fin.last k)))
    (placed : CodeAt target pc (endingCode original pc)) :
    ∃ n ≤ endingCost m d B k, ∃ z, Execution target (scalarBound (decoderLimit d H))
      (s.atPC (firstReturn pc 0)) n z ∧ OptimizationOutput A b c z

private theorem finish_trace {p : Program} {T U : Polynomial Nat} {m d L H k : Nat}
    {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {c : Fin d → ℚ} {z : State ℚ}
    (run : Execution p (scalarBound H) (start [m,d] (lpInput A b ++ List.ofFn c)) k z)
    (ht : k ≤ T.eval (m+d)) (hu : H ≤ U.eval L) (hz : OptimizationOutput A b c z) :
    ∃ (k : Nat) (t : Fin (k+1) → State ℚ), Trace p (start [m,d] (lpInput A b ++ List.ofFn c)) k t ∧
      k ≤ polyBound (T.eval 1) T.natDegree (m+d) ∧ (∀ i, scalarBound (polyBound (U.eval 1) U.natDegree L) (t i)) ∧
      OptimizationOutput A b c (t (Fin.last k)) := by
  obtain ⟨t,tr,last,safe⟩ := run.to_trace
  exact ⟨k,t,tr,ht.trans (polynomial_eval_le_polyBound _ _),
    fun i j => (safe i j).trans (hu.trans (polynomial_eval_le_polyBound _ _)),by rw [last]; exact hz⟩

/-- Two ordinary calls, three physical return paths and a uniform pair of time and
bit polynomials. The program, and all four constants, are chosen before the input. -/
theorem optimization_of_verified_return_paths (firstReturn : Nat → Nat → Nat)
    (endingCode : Program → Nat → Program) (handler : VerifiedEnding firstReturn endingCode)
    (feasibility : StronglyPolynomialFeasibility) : StronglyPolynomialOptimization := by
  obtain ⟨p,C₀,E,bC,bE,solve⟩ := feasibility
  let off := firstReturnBase p C₀ E
  let code := withFirstCall p C₀ E firstReturn (endingCode p)
  let firstBudget := firstTimePolynomial p C₀ E
  let window := firstWindowPolynomial p C₀ E
  let secondBudget := oraclePolynomial C₀ E
  let finalBudget := endingPolynomial window secondBudget
  let time := firstBudget+finalBudget
  let bits := optimizationBitsPolynomial bC bE
  refine ⟨code,time.eval 1,time.natDegree,bits.eval 1,bits.natDegree,?_⟩
  intro m d hm hd A b c
  let xs := lpInput A b
  let obj := List.ofFn c
  let L := totalBits (xs++obj)
  let H := (calleeBitsPolynomial bC bE).eval L
  let B := firstLimit p C₀ E m d
  obtain ⟨h3,_,inputSafe,firstBits,jointBits⟩ := callee_bits A b c bC bE
  have hzero : ratBits 0 ≤ H := by exact h3
  have firstCode := withFirstCall_locations p C₀ E firstReturn (endingCode p)
  obtain ⟨k,tr,runk,hk,small,result⟩ := solve m d hm hd A b
  let last := tr (Fin.last k)
  obtain ⟨tag,done⟩ : ∃ tag, last.output=some tag := result.elim (fun h => ⟨0,h.1⟩) (fun h => ⟨1,h.1⟩)
  have hx : xs.length = primalLength m d := lpInput_length A b
  have hy : obj.length=d := List.length_ofFn
  obtain ⟨n,hn,s,first,frm⟩ := normal_first_call (P := fun q : ℚ => ratBits q ≤ H) p C₀ E m d xs obj hx hy hzero (fun j => inputSafe j)
    firstCode.1 firstCode.2.1 tr runk hk (fun i j => (small i j).trans firstBits) done
  have nBound : n ≤ firstBudget.eval (m+d) := hn.trans (firstTime_bound p C₀ E m d k hk)
  have BBound : B ≤ window.eval (m+d) := firstWindow_bound p C₀ E m d
  have LBound : d ≤ L := (Nat.le_add_left d m).trans (dimensions_le_optInputBits A b c)
  have scalarMax : decoderLimit d H ≤ bits.eval L := optimization_scalar_bound bC bE d L LBound
  have initialExecution := first.weaken (Q := scalarBound (decoderLimit d H))
    (fun _ h j => (h j).trans (decoderLimit_bounds d H).1)
  have combine {t : Nat} {z : State ℚ} {u : Nat}
      (back : Execution code (scalarBound (decoderLimit d H)) (s.atPC (firstReturn off tag)) t z)
      (tc : t ≤ endingCost m d B u) (tk : u ≤ secondBudget.eval (m+d)) (answer : OptimizationOutput A b c z) :
      ∃ (j : Nat) (a : Fin (j+1) → State ℚ), Trace code (start [m,d] (xs++obj)) j a ∧
        j ≤ polyBound (time.eval 1) time.natDegree (m+d) ∧
        (∀ i, scalarBound (polyBound (bits.eval 1) bits.natDegree L) (a i)) ∧ OptimizationOutput A b c (a (Fin.last j)) := by
    have tc' : t ≤ finalBudget.eval (m+d) := tc.trans (endingCost_le window secondBudget m d B u BBound tk)
    apply finish_trace (T:=time) (U:=bits) (L:=L) (initialExecution.append back) _ scalarMax answer
    simpa only [time,eval_add] using Nat.add_le_add nBound tc'
  rcases result with ⟨h0,feas⟩ | ⟨h1,cert⟩
  · have tag0 : tag=0 := Option.some.inj (done.symm.trans h0)
    subst tag
    obtain ⟨k₂,tr₂,secondRun,hk₂,small₂,out₂⟩ := solve (rowCount m d) (d+m)
      (by unfold rowCount; omega) (by omega) (finJointMatrix A b c) (finJointRhs b c)
    have len : (xs++obj).length=origLen m d := by simp [xs,obj,lpInput_length,origLen]
    obtain ⟨t,ht,z,returned,output⟩ := handler.feasible A b c (readVector last 0 d) feas s first.safe_end
      h3 frm.rows frm.cols frm.limit (fun i hi => frm.original i (by simpa only [len] using hi))
      (fun i => by simpa [readVector] using frm.result i.val)
      (fun i hi => (frm.vacant (2*i) (by change 2*B+2 ≤ 2*i; omega)).1)
      (fun i hi => (frm.vacant (2*i) (by change 2*B+2 ≤ 2*i; omega)).2)
      tr₂ secondRun (fun i j => (small₂ i j).trans jointBits) out₂ firstCode.2.2
    exact combine returned ht (hk₂.trans_eq (joint_time_eval _ _ _ _)) output
  · have tag1 : tag=1 := Option.some.inj (done.symm.trans h1)
    subst tag
    obtain ⟨t,ht,z,returned,output⟩ := handler.certificate (B:=B) A b c last cert s first.safe_end
      frm.rows frm.cols frm.result firstCode.2.2
    exact combine returned ht (Nat.zero_le _) output

end PrimalDual
end LinearProgramming
end Optimization
end OAI
