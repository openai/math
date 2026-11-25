import OAI.Computability.MultitapeWeakETH.HistoryVisitBounds

/-! # Clock and storage constants for the witness walk at the sparse volume -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords PairSimulation LocalHistory
open NodeArguments WitnessWalk DyadicBudget
open private passes_bound input_size from OAI.Computability.MultitapeWeakETH.HistoryVisitBounds

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
  {f : B.Entry → R} {hf : B.IsSolution f}

noncomputable def visitFuel (N : ℕ) := (2^(4*stepSize B)*N)^((B.recordLimit+1)*(S.steps+1))

variable {B} (H : ResidentHistory B f hf)

theorem history_fuel (big : 1 < H.volume.length) :
    (B.recordLimit+1)^H.passes.length ≤ visitFuel B H.volume.length := by
  let s := gridIndex B H.volume
  let b := 4*stepSize B
  let d := B.recordLimit+1
  have hb : 0 < b := by have := step_pos B; dsimp [b]; omega
  have grid : 2^s ≤ 2^b*H.volume.length :=
    (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left s hb)).trans (grid_cover hb big).2
  calc
    d^H.passes.length ≤ d^((S.steps+1)*s) := Nat.pow_le_pow_right (Nat.succ_pos _) (passes_bound H)
    _ ≤ (2^d)^((S.steps+1)*s) := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _
    _ = (2^s)^(d*(S.steps+1)) := by simp only [← pow_mul]; congr 1; ring
    _ ≤ (2^b*H.volume.length)^(d*(S.steps+1)) := Nat.pow_le_pow_left grid _

private theorem final_within {a g b l P M : ℕ} {X : State a g} (E : StateExecution R b l X)
    (z : E.Choices) (bound : PrefixLevelScale.Within P M E) :
    (E.finalState z).positions ≤ P ∧ (E.finalState z).maxWireWidth ≤ M := by
  induction E with
  | done => exact bound
  | more p tail ih => exact ih z.1 z.2 (bound.2.2 z.1)

theorem final_job_size (big : 1 < H.volume.length) (fits : max 1 (slotDegree S) ≤ gridIndex B H.volume) :
    let Y := (gridExecution B f hf H.volume).finalState H.path
    ∀ v h, size (inputJob Y H.passes.length v h) ≤ jobRoom B H.volume.length := by
  intro Y v h
  let s := gridIndex B H.volume
  have one : 1 ≤ s := (le_max_left ..).trans fits
  have cap := scale_polynomial B big
  have sSmall := (scale_ge B s).trans cap
  obtain ⟨pos,width⟩ := final_within (gridExecution B f hf H.volume) H.path (within B f hf one)
  have deg : 2^S.degreeExponent 0 ≤ slotDegree S :=
    (Finset.le_sup (f := fun i : Fin (S.steps+1) => 2^S.degreeExponent i) (Finset.mem_univ 0)).trans (le_max_right ..)
  have bound := input_size B Y H.passes.length H.volume.length v h
    ((passes_bound H).trans (Nat.mul_le_mul_left _ sSmall)) (pos.trans ((source_positions B one).trans cap))
    (deg.trans (((le_max_right ..).trans fits).trans sSmall)) (width.trans cap)
  exact bound.trans (by unfold jobRoom; rw [Nat.mul_succ]; omega)

end OAI.Computability.MultitapeWeakETH.NativeGrid
