import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectTape
import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifySelected
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBankNative

/-! # Selected grouped-stage packets in the repair leaf ABI -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template.Data

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims InterchangeROMTable InterchangeROMRepair
  InterchangeROMRepair.Physical InterchangeROMStage Space InterchangeROM

variable {j threshold f : ℕ} {x : Template.Data} {P G S : Dims.Tape} {D : Type}
  [Fact (x.modulusIndex+1).Prime] [NeZero x.b]

/-- The actual bank of ragged scalar-lane streams at one point in the selected trajectory. -/
noncomputable def stateTape (h : Valid j threshold x) (rows : Series (x.Address P G S f))
    (pay : Series D) (v : x.Wide P G S f D) (n : ℕ) : Tree :=
  (roleRealization h).Tape n (Raw.rowCount x.m) (fun w i =>
    stripe rows fun a => stripe pay fun d => numeral (stageStates h v n w (a,d) i).val)

theorem stateTape_initial (h : Valid j threshold x) (rows : Series (x.Address P G S f))
    (pay : Series D) (v : x.Wide P G S f D) :
    stateTape h rows pay v 0 = Task.forest id (SweepBank.packed rows pay v) :=
  (roleRealization h).start_tape_bank rows (fun _ => pay) (fun a d => (a,d)) v

theorem stateTape_final (h : Valid j threshold x) (rows : Series (x.Address P G S f))
    (pay : Series D) (v : x.Wide P G S f D) :
    stateTape h rows pay v 11 = Task.forest id (SweepBank.packed rows pay (stagePayload h v)) := by
  unfold stateTape
  rw [stageStates_stagePayload h]
  exact (roleRealization h).end_tape_bank rows (fun _ => pay) (fun a d => (a,d)) (stagePayload h v)

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
