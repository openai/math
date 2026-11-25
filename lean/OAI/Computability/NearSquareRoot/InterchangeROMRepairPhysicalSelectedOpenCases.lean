import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedSweepOpen
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedCorrectionOpen

/-! # The four routed leaves of the selected Hermite program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims InterchangeAddress Interchange.Template
  InterchangeROMStageVolume

/-- Every routed native transition carries its own recorded child list and
a local charge with one computable template coefficient. Only the local
allowance uses the polynomially enlarged width. -/
theorem routed_open : ∃ e : ℕ, 1 ≤ e ∧ ∃ K : Data → ℕ, Computable K ∧
    ∀ {j threshold f w : ℕ} {x : Data} [NeZero x.b] [Fact (x.modulusIndex+1).Prime]
      (h : Data.Valid j threshold x) {P G S : Tape} (_ : ∀ k∈P++G++S, 2≤k ∧ k≤x.b)
      {D : Type} (pay : Series D) (_ : pay.count ≤ w) (a : Leaf) (src dst : List Tree)
      (_ : LocalTable.Lift.Routed a) (_ : transfer h P G S f pay a src dst),
      let hdr := InterchangeROMAddress.header f P G S
      let width := w+(size hdr+1)^e
      let M := mass (send hdr) (x.stageRows P G S f).count width
      LeafStep h P G S f pay w (K x*M) a src dst := by
  obtain ⟨e,he,chart,hchart,runChart⟩ := chart_step_enlarged
  obtain ⟨correct,hcorrect,runCorrect⟩ := selected_correction_leafStep
  let K := fun x : Data => max (chart x) (max (sweepFactor x) (correct x))
  have hK : Computable K := Primrec.nat_max.to_comp.comp hchart
    (Primrec.nat_max.to_comp.comp computable_sweepFactor hcorrect)
  refine ⟨e,he,K,hK,?_⟩
  intro j threshold f w x nz prime h P G S ok D pay hw a src dst route tr
  let hdr := InterchangeROMAddress.header f P G S
  let W := w+(size hdr+1)^e
  let N := (x.stageRows P G S f).count
  let M := mass (send hdr) N W
  have hM : mass (send hdr) N w ≤ M := by
    have := Nat.mul_le_mul_left N (show w+1 ≤ W+1 by dsimp [W]; omega)
    dsimp only [M,InterchangeROMStageVolume.mass]
    omega
  have hc : chart x*M ≤ K x*M := Nat.mul_le_mul_right M (le_max_left ..)
  have hs : sweepFactor x*mass (send hdr) N w ≤ K x*M :=
    Nat.mul_le_mul ((le_max_left ..).trans (le_max_right ..)) hM
  have ht : correct x*mass (send hdr) N w ≤ K x*M :=
    Nat.mul_le_mul ((le_max_right ..).trans (le_max_right ..)) hM
  have hp : solid P := fun k hk => (ok k (by simp [hk])).1
  have hg : solid G := fun k hk => (ok k (by simp [hk])).1
  have hb : solid S := fun k hk => (ok k (by simp [hk])).1
  cases tr with
  | stage z => exact (runChart h P G S hp hg hb pay hw z).toLeaf.mono hc
  | forward y z => exact (sweep_leaves h ok pay hw false y z).mono hs
  | backward y z => exact (sweep_leaves h ok pay hw true y z).mono hs
  | correct y z => exact (runCorrect x h P G S ok f pay w hw y z).mono ht
  | duplicate | extract | restore | copyCube | finish => exact False.elim route

end InterchangeROMRepair.Physical.Selected

end NearSquareRoot
end Computability
end OAI
