import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectBudget

/-! # Leaf-wise open execution on a selected native repair bank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims InterchangeAddress Interchange.Template InterchangeROM

/-- A leaf supplies a concrete list of valid recursive requests together with
its execution for arbitrary individual allowances on those requests. -/
abbrev LeafStep {j threshold : ℕ} {x : Data} [NeZero x.b] [Fact (x.modulusIndex+1).Prime]
    (h : Data.Valid j threshold x) (P G S : Tape) (f : ℕ) {D : Type} (pay : Series D)
    (width bound : ℕ) (a : Leaf) (u v : List Tree) :=
  let hdr := send (InterchangeROMAddress.header f P G S)
  ∃ qs : List (Request x.b), qs.length ≤ phaseCalls h a ∧
    (∀ q∈qs, OpcodeProgram.Valid f (x.stageRows P G S f).count width P G S (x.recordGood pay) q) ∧
    InterchangeROMSequence.Step (Request.job x.b) (commands x a) hdr (Task.forest id u) (packet hdr v)
      qs bound bound bound

theorem LeafStep.mono {j threshold f w A B : ℕ} {x : Data} [NeZero x.b] [Fact (x.modulusIndex+1).Prime]
    {h : Data.Valid j threshold x} {P G S : Tape} {D : Type} {pay : Series D}
    {a : Leaf} {u v : List Tree} (s : LeafStep h P G S f pay w A a u v) (b : A ≤ B) :
    LeafStep h P G S f pay w B a u v := by
  obtain ⟨qs,len,valid,run⟩ := s
  exact ⟨qs,len,valid,run.mono b b b⟩

theorem ChartStep.toLeaf {j threshold f w B : ℕ} {x : Data} [NeZero x.b] [Fact (x.modulusIndex+1).Prime]
    {h : Data.Valid j threshold x} {P G S : Tape} {D : Type} {pay : Series D} {z : x.Wide P G S f D}
    (step : ChartStep h P G S pay w B z) :
    LeafStep h P G S f pay w B .stage (wideBank x P G S f pay z) (wideBank x P G S f pay (Data.stagePayload h z)) := by
  obtain ⟨qs,len,valid,run⟩ := step
  refine ⟨qs,?_,valid,run⟩
  rw [len,Data.literalStageCharge_eq h]
  exact le_rfl

end InterchangeROMRepair.Physical.Selected

end NearSquareRoot
end Computability
end OAI
