import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectWordUniform
import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectBank
import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectActive
import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectWordLedger
import OAI.Computability.NearSquareRoot.InterchangeROMStageStep
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelected

/-! # Open recursion for the grouped predictor on the selected repair banks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace Interchange.Template.Data

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Loom
  InterchangeAddress InterchangeROMStage InterchangeROMStageVolume InterchangeROMSequence
  InterchangeROMRepair InterchangeROMRepair.Physical InterchangeROMTable
  InterchangeSpectralFibre Space

/-- Every recursive request here is an actual entry of the concatenated six-pass
ledger. Its price is bounded by the selected chart, with no ceiling per scalar lane. -/
theorem selected_stage_step : ∃ M C K e : ℕ, 1 ≤ e ∧ ∀ {j threshold f l : ℕ}
    {x : Data} [NeZero x.b] [Fact (x.modulusIndex+1).Prime]
    (h : Valid j threshold x) (P G S : Tape) (_ : solid P) (_ : solid G) (_ : solid S)
    {D : Type} (pay : Series D) (v : x.Wide P G S f D),
    let hdr := InterchangeROMAddress.header f P G S
    let rows := x.stageRows P G S f
    let F := rowFactor M C K e x * rowMass e hdr rows.count pay.count
    let m := mass (send hdr) rows.count pay.count
    ∃ qs, qs.length = x.literalStageCharge ∧
      (∀ q∈qs, OpcodeProgram.Valid (b:=x.b) f rows.count l P G S (x.recordGood pay) q) ∧
      Step (Request.job x.b) (Selected.stage x) (send hdr)
        (Task.forest id (SweepBank.packed rows pay v))
        (InterchangeROM.packet (send hdr) (SweepBank.packed rows pay (stagePayload h v))) qs
        (stageFactor x.stageParameters*m+fieldCount x.roleFrame (Raw.rowCount x.m)*F)
        (localFactor x.stageParameters*m+F) (localFactor x.stageParameters*m+F+1) := by
  obtain ⟨M,C,K,e,he,H⟩ := selected_state_uniform
  refine ⟨M,C,K,e,he,?_⟩
  intro j threshold f l x nz hp h P G S hP hG hS D pay v
  let r := roleRealization h
  let N := Raw.rowCount x.m
  let hdr := InterchangeROMAddress.header f P G S
  let rows := x.stageRows P G S f
  let F := rowFactor M C K e x * rowMass e hdr rows.count pay.count
  let law := fun (k : Fin 6) (z : r.Field N k) =>
    H (l:=l) h P G S hP hG hS pay v k z.1 z.2
  choose qs len valid moves using law
  refine ⟨r.ledger N qs,ledger_eq_literal h qs len,?_,?_⟩
  · intro q hq
    obtain ⟨k,z,hz⟩ := (r.mem_ledger _).mp hq
    exact valid k z q hz
  · let pi : r.NativeMove → Equiv.Perm (x.Address P G S f × D) := (withPayload D (nativeLayout h P G S f)).perm
    let : Fact x.stageParameters.2.1.Prime := hp
    have stage := InterchangeROMStage.step x.stageParameters r rows pay pi v
      (Request.job x.b) x.chart x.wordCmd (send hdr) qs F F F (stage_active h)
      (fun k z d => moves k (z,d))
    change Step _ (Selected.stage x) _ (stateTape h rows pay v 0)
      (.fork (send hdr) (stateTape h rows pay v 11)) _ _ _ _ at stage
    rw [stateTape_initial,stateTape_final] at stage
    exact stage

end Interchange.Template.Data

end

end NearSquareRoot
end Computability
end OAI
