import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionWeightSize

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass Moment

variable {N ne : ℕ}

/-- An internal call's exact schedule, before its terminal assembly map. -/
def weightSchedule (r R : ℕ) (experts : Fin ne → Expert N) (fuel l : ℕ)
    (path : States.Path (Fin N) (Vertex N l)) (history : History N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) : Computation N (NodeRun experts w r l) :=
  let solve := marketSolverAtCommonWeightUnit experts
  let child := fun (y : Prices N l) (dw : Weights ne) (hdw : ∀ e, 0 ≤ dw e) =>
    execute r R experts solve fuel (l+1) (.extend path y (vertexDecidableEq N l))
      (history.push l y) dw hdw
  runSchedule (fun _ xs c => StepOK experts w xs c)
    (executeStep experts solve w hw history path child) (2*r)

theorem execute_eq_weightSchedule (r R : ℕ) (experts : Fin ne → Expert N) (fuel l : ℕ)
    (path : States.Path (Fin N) (Vertex N l)) (history : History N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) :
    execute r R experts (marketSolverAtCommonWeightUnit experts) (fuel+1) l path history w hw =
      (weightSchedule r R experts fuel l path history w hw).map (assemble experts history w) := rfl

/-- Bounds the reduced encoding and integrality grid for *each* input, local and deeper
weight at *each* prefix of *each* visited node. The guard admits both responses at
each query. The child is entered at its recorded baseline with the replayed deeper inputs. -/
def WeightRegistersWithin (r R : ℕ) (experts : Fin ne → Expert N) (Q localQ bits : ℕ) :
    (fuel l : ℕ) → States.Path (Fin N) (Vertex N l) → History N →
      (w : Weights ne) → (∀ e, 0 ≤ w e) → Prop
  | 0, _, _, _, w, _ => ∀ e, (w e).den ∣ Q ∧ RAM.ratBits (w e) ≤ bits
  | fuel+1, l, path, history, w, hw =>
    (∀ e, (w e).den ∣ Q ∧ RAM.ratBits (w e) ≤ bits) ∧
    (weightSchedule r R experts fuel l path history w hw).Guarded (fun _ => True) (fun xs =>
      (∀ t (ht : t ≤ 2*r) (e : Fin ne),
        let prior :=  takePrefix xs.val t ht
        let localW := incomingLocal experts w prior e
        let deepW := incomingDeep experts w prior e
        (localW.den ∣ localQ ∧ RAM.ratBits localW ≤ bits) ∧
          (deepW.den ∣ Q ∧ RAM.ratBits deepW ≤ bits)) ∧
      ∀ j : Fin (2*r),
        let prior :=  TrialExecution.«prefix» xs.val j
        let y := (xs.val j).data.baseline
        WeightRegistersWithin r R experts Q localQ bits fuel (l+1) (.extend path y (vertexDecidableEq N l))
          (history.push l y) (incomingDeep experts w prior) (incomingDeep_nonneg experts w hw prior))

/-- One layer can accumulate at most this many bits from child score multipliers. -/
def weightLayerBits (N r : ℕ) : ℕ := (2*r) * (2*N)^274

/-- A uniform bound for all routed rationals, at their actual addresses, across the whole
trial. The last parameters are the initial magnitude and denominator bit budgets. -/
def weightBits (N r fuel b d : ℕ) : ℕ :=
  3 + (b + fuel * weightLayerBits N r + r) + 2 * (d + learningRateBits*r)

private theorem outputs_weaken {A : Type*} {p : Computation N A} {P S : A → Prop}
    (hp : p.AllOutputs P) (hs : ∀ a, P a → S a) : p.AllOutputs S := by
  induction hp with
  | pure ha => exact .pure (hs _ ha)
  | ask _ ih => exact .ask ih

private theorem weightsWithin_aux (r R : ℕ) (experts : Fin ne → Expert N)
    (Q d top : ℕ) (hQ : 0 < Q) (hden : Q ≤ 2^d) (hN : 0 < N) :
    ∀ fuel, fuel ≤ depth N → ∀ l (path : States.Path (Fin N) (Vertex N l))
      (history : History N) (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (b : ℕ),
      WeightInputCap Q b w → b + fuel * weightLayerBits N r ≤ top →
      WeightRegistersWithin r R experts Q (Q*etaQ.den^r) (3+(top+r)+2*(d+learningRateBits*r))
        fuel l path history w hw := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ l path history w hw b cap htop e
    have hbit := cap.ratBits hQ hden hw e
    refine ⟨cap.den e, ?_⟩
    simp only [Nat.zero_mul, Nat.add_zero] at htop
    omega
  | succ fuel ih =>
    intro hdepth l path history w hw b cap htop
    have hnext : b + weightLayerBits N r + fuel * weightLayerBits N r ≤ top := by
      rw [Nat.succ_mul] at htop
      omega
    have hbegin : b ≤ top := by omega
    constructor
    · intro e
      have hbit := cap.ratBits hQ hden hw e
      exact ⟨cap.den e, by omega⟩
    let solve := marketSolverAtCommonWeightUnit experts
    let child := fun (y : Prices N l) (dw : Weights ne) (hdw : ∀ e, 0 ≤ dw e) =>
      execute r R experts solve fuel (l+1) (.extend path y (vertexDecidableEq N l))
        (history.push l y) dw hdw
    have hlocal := schedule_localWeightBudget experts w hw history path child Q cap.den (2*r)
    have hscore : ∀ y dw hdw, (child y dw hdw).AllOutputs (fun c => c.val.trace.height ≤ depth N) := by
      intro y dw hdw
      have hf := execute_all_trace_height r R experts solve fuel (l+1)
        (.extend path y (vertexDecidableEq N l)) (history.push l y) dw hdw
      exact outputs_weaken hf (fun _ h => h.trans (Nat.le_of_succ_le hdepth))
    have hdeep := schedule_deepWeightCap experts solve w hw history path child hscore cap hN (2*r)
    apply Computation.guarded_mono (Computation.guarded_and hlocal hdeep) (fun _ _ => True.intro)
    intro xs both
    have hinc (t : ℕ) (ht : t ≤ 2*r) : b + t*(2*N)^274 ≤ b + weightLayerBits N r :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) _
    constructor
    · intro t ht e
      have hloc := both.1 t ht
      have hdep := both.2 t ht
      have hlocbit := hloc.ratBits hQ hden cap.upper
        (incomingLocal_nonneg experts w hw (takePrefix xs.val t ht)) e
      have hdepbit := hdep.ratBits hQ hden (incomingDeep_nonneg experts w hw (takePrefix xs.val t ht)) e
      have hdenlocal := (hloc.den e).trans (Nat.mul_dvd_mul_left Q (pow_dvd_pow etaQ.den (Nat.min_le_right t r)))
      have hpr := hinc t ht
      exact ⟨⟨hdenlocal, by omega⟩, ⟨hdep.den e, by omega⟩⟩
    · intro j
      have dcap := both.2 j.val j.isLt.le
      apply ih (Nat.le_of_succ_le hdepth) (l+1)
        (.extend path (xs.val j).data.baseline (vertexDecidableEq N l))
        (history.push l (xs.val j).data.baseline)
        (incomingDeep experts w (TrialExecution.«prefix» xs.val j))
        (incomingDeep_nonneg experts w hw _) (b+j.val*(2*N)^274)
      · exact dcap
      · have hpr := hinc j.val j.isLt.le
        omega

theorem weightRegistersWithin_of_cap (r R : ℕ) (experts : Fin ne → Expert N)
    (fuel l : ℕ) (path : States.Path (Fin N) (Vertex N l)) (history : History N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) {Q b d : ℕ} (hQ : 0 < Q)
    (hden : Q ≤ 2^d) (cap : WeightInputCap Q b w) (hN : 0 < N) (hfuel : fuel ≤ depth N) :
    WeightRegistersWithin r R experts Q (Q*etaQ.den^r) (weightBits N r fuel b d)
      fuel l path history w hw :=
  weightsWithin_aux r R experts Q d _ hQ hden hN fuel hfuel l path history w hw b cap le_rfl

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
