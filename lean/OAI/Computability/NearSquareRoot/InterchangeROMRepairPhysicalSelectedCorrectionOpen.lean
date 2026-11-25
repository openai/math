import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalCorrectionSelected
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedLeafStep

/-! # The empty recursive ledger of the selected Hermite correction -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port Space
  InterchangeAddress InterchangeROMAddress InterchangeROM Interchange.Template

set_option maxRecDepth 8192

/-- The selected correction uses only its local generated table on both
packed check banks. Its execution accepts arbitrary child prices. -/
theorem selected_correction_step :
    ∃ C E H : ℕ, ∀ (x : Data) [Fact (x.modulusIndex+1).Prime] [NeZero x.b]
      {j threshold : ℕ} (_ : Data.Valid j threshold x) (P G S : Tape)
      (_ : ∀ k ∈ P ++ G ++ S, 2 ≤ k ∧ k ≤ x.b) (f : ℕ) {D : Type}
      (pay : Series D) (width : ℕ) (_ : pay.count ≤ width)
      (u v : x.Short P G S f D),
      let hdr := send (header f P G S)
      let price := correctFactor C E H x * InterchangeROMStageVolume.mass hdr (x.stageRows P G S f).count width
      let short := shortBank x P G S f pay
      let op := applyTag x.spec (flags ∘ Prod.fst)
      InterchangeROMSequence.Step (Request.job x.b) (commands x .correct) hdr (Task.forest id (short u ++ short v))
        (packet hdr (short (op false u v) ++ short (op true u v))) [] price price price := by
  obtain ⟨C,E,H,run⟩ := correct_transition
  refine ⟨C,E,H,?_⟩
  intro x prime nz j threshold valid P G S ok f D pay width hw u v hdr price short op
    parent env time data depth _ deck base cap
  simp only [List.map_nil,List.sum_nil,InterchangeSpace.childPeak,List.foldr_nil,Nat.add_zero]
  exact run x valid P G S ok f pay width hw u v (parent::env) deck base cap

/-- A single computable coefficient pays for the local leaf in the open
repair script, uniformly in the native layout and payload width. -/
theorem selected_correction_leafStep :
    ∃ K : Data → ℕ, Computable K ∧ ∀ (x : Data) [Fact (x.modulusIndex+1).Prime] [NeZero x.b]
      {j threshold : ℕ} (h : Data.Valid j threshold x) (P G S : Tape)
      (_ : ∀ k ∈ P ++ G ++ S, 2 ≤ k ∧ k ≤ x.b) (f : ℕ) {D : Type}
      (pay : Series D) (width : ℕ) (_ : pay.count ≤ width) (u v : x.Short P G S f D),
      let hdr := send (header f P G S)
      let price := K x * InterchangeROMStageVolume.mass hdr (x.stageRows P G S f).count width
      let short := shortBank x P G S f pay
      let op := applyTag x.spec (flags ∘ Prod.fst)
      LeafStep h P G S f pay width price .correct (short u ++ short v)
        (short (op false u v) ++ short (op true u v)) := by
  obtain ⟨C,E,H,step⟩ := selected_correction_step
  refine ⟨correctFactor C E H,computable_correctFactor C E H,?_⟩
  intro x prime nz j threshold h P G S ok f D pay width hw u v
  exact ⟨[],Nat.zero_le _,by simp,step x h P G S ok f pay width hw u v⟩

end InterchangeROMRepair.Physical.Selected

end NearSquareRoot
end Computability
end OAI
