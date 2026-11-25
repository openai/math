import OAI.Hierarchy.ProtocolRAMCalendarThreshold

namespace OAI
/-! # A genuine paid-purchase opcode implies positive score or injection excess -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open AttemptGate PurchaseStage
open scoped BigOperators Fin.CommRing
noncomputable section

variable {w q d : ℕ}

/-- The score and payload prefix sums are tested against two successive native
memories; the injection bit itself comes from the fixed mesh calendar. -/
theorem observed_purchased (C : Chart w q d) (mem : Memory w) (p h : ℕ)
    (layout : TestRoom (repair C (.outer p h)) w) (hit : observedMode C mem p h=3) :
    let a := Attempt.outer p h
    let B := repair C a
    let m := prepared C a (trialState C mem p h)
    B.tests.excess.high m=true ∨ (p<C.mesh.inject ∧ B.tests.payload.high (B.tests.excess.after m)=true) := by
  intro a B m
  change actual B.policy (postSnapshot (C.layout a) B m)=3 at hit
  rw [post_result _ _ _ layout] at hit
  change selectMode B.tests.injection false _ _ _ _=3 at hit
  have split (inj stop excess payload disc : Bool) (mode : selectMode inj false stop excess payload disc=3) :
      excess=true ∨ (inj=true ∧ payload=true) := by
    cases inj <;> cases stop <;> cases excess <;> cases payload <;> cases disc <;> simp_all [selectMode]
  rcases split _ _ _ _ _ hit with x | ⟨y,z⟩
  · exact Or.inl x
  · exact Or.inr ⟨of_decide_eq_true y,z⟩

/-- The true total dominates the high threshold of the installed word sum. -/
theorem SumCalibration.high {z : Check} {m : Memory w} {total cap : ℝ}
    (R : SumCalibration z m total cap) (vote : z.high m=true) : R.threshold≤total := by
  have big := (threshold_bounds R.value R.value_nonneg R.precision R.positive R.threshold R.threshold_nonneg).1
  have up : z.bound≤∑i,z.score m i := of_decide_eq_true vote
  rw [R.bound] at up
  simp only [R.words] at up
  simpa only [R.sum_eq] using big up

/-- Source of the strict disjunction for the exact `AdaptiveProbe.trigger_motion`.
No rounded maximizer or abstract high/low Boolean appears in the conclusion. -/
theorem observed_excess (C : Chart w q d) (mem : Memory w) (p h : ℕ)
    (layout : TestRoom (repair C (.outer p h)) w) (hit : observedMode C mem p h=3)
    (n barrier s score payload cost cap : ℝ) (npos : 0<n) (injected : p<C.mesh.inject → s=1) :
    let a := Attempt.outer p h
    let B := repair C a
    let m := prepared C a (trialState C mem p h)
    ∀ X : SumCalibration B.tests.excess m score cost,
    ∀ Y : SumCalibration B.tests.payload (B.tests.excess.after m) payload cap,
    X.threshold=n*(barrier+3/8) → Y.threshold=n*(1+3/8) →
    barrier < score/n ∨ (s=1 ∧ n<payload) := by
  intro a B m X Y xcut ycut
  rcases observed_purchased C mem p h layout hit with x | ⟨inj,y⟩
  · left; apply (lt_div_iff₀ npos).2
    have paid := X.high x
    rw [xcut] at paid; nlinarith only [paid,npos]
  · refine Or.inr ⟨injected inj,?_⟩
    have paid := Y.high y
    rw [ycut] at paid; linarith

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
