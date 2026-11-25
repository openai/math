import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectStep
import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectFactor
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedRelease

/-! # The selected chart on a complete native repair bank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Loom
  InterchangeAddress InterchangeROMStageVolume InterchangeROMSequence
  Interchange.Template Space InterchangeROM

theorem layout_nonempty {x : Data} [NeZero x.b] {f : ℕ} {P G S : Tape}
    (hP : solid P) (hG : solid G) (hS : solid S) (hb : 2 ≤ x.b) :
    0 < (x.stageRows P G S f).count := by
  let pin (L : Tape) (ok : solid L) : Pin L :=
    (Dims.layout L).follow ⟨0,by simpa only [Dims.space] using Dims.wide L ok⟩
  have fields (t : ℕ) : solid (Adic.field x.b t) := by
    induction t with
    | zero => simp [Adic.field,solid]
    | succ t ih => exact (solid_cons ..).mpr ⟨hb,ih⟩
  let digit := pin (Adic.field x.b f) (fields f)
  let a : x.Address P G S f := (pin P hP, fun _ => digit, pin G hG, fun _ => digit, pin S hS)
  exact Nat.zero_lt_of_lt ((x.stageRows P G S f).index a).isLt

/-- The literal stage calls its recorded children, whose record width is the
inherited user width. The local budget may charge a larger width. -/
abbrev ChartStep {j threshold f : ℕ} {x : Data} [NeZero x.b] [Fact (x.modulusIndex+1).Prime]
    (h : Data.Valid j threshold x) (P G S : Tape) {D : Type} (pay : Series D)
    (childWidth localBound : ℕ) (z : x.Wide P G S f D) :=
  let hdr := send (InterchangeROMAddress.header f P G S)
  let N := (x.stageRows P G S f).count
  ∃ qs : List (Request x.b), qs.length = x.literalStageCharge ∧
    (∀ q∈qs, OpcodeProgram.Valid (b:=x.b) f N childWidth P G S (x.recordGood pay) q) ∧
    InterchangeROMSequence.Step (Request.job x.b) (stage x) hdr
      (Task.forest id (wideBank x P G S f pay z))
      (packet hdr (wideBank x P G S f pay (Data.stagePayload h z))) qs localBound localBound localBound

/-- A single computable chart coefficient works both for already thick records
and for the enlarged local mass at arbitrary widths. -/
theorem chart_step : ∃ e : ℕ, 1 ≤ e ∧ ∃ K : Data → ℕ, Computable K ∧
    ∀ {j threshold f width localWidth : ℕ} {x : Data} [NeZero x.b] [Fact (x.modulusIndex+1).Prime]
      (h : Data.Valid j threshold x) (P G S : Tape) (_ : solid P) (_ : solid G) (_ : solid S)
      {D : Type} (pay : Series D) (_ : pay.count ≤ localWidth)
      (_ : (size (InterchangeROMAddress.header f P G S)+1)^e ≤ localWidth+1) (z : x.Wide P G S f D),
      let H := send (InterchangeROMAddress.header f P G S)
      ChartStep h P G S pay width (K x * mass H (x.stageRows P G S f).count localWidth) z := by
  obtain ⟨M,C,K,e,he,run⟩ := Data.selected_stage_step
  refine ⟨e,he,Data.chartFactor M C K e,Data.computable_chartFactor M C K e,?_⟩
  intro j threshold f width localWidth x nz prime h P G S p g s D pay hw hpow z
  let hdr := InterchangeROMAddress.header f P G S
  let N := (x.stageRows P G S f).count
  obtain ⟨qs,ln,valid,stage⟩ := run (l:=width) h P G S p g s pay z
  have hn : 0<N := layout_nonempty p g s (Data.radix_gt_one h)
  obtain ⟨hm,hU,hB⟩ := Data.chart_mass_thick e hdr N pay.count localWidth hn hw hpow
  obtain ⟨ht,hs,hd⟩ := Data.chart_bounds M C K e x hm hU hB
  exact ⟨qs,ln,valid,stage.mono ht hs hd⟩

/-- Unconditional version. Polynomial header overhead is charged solely in
the local mass. The child width in every transmitted request stays unchanged. -/
theorem chart_step_enlarged : ∃ e : ℕ, 1 ≤ e ∧ ∃ K : Data → ℕ, Computable K ∧
    ∀ {j threshold f width : ℕ} {x : Data} [NeZero x.b] [Fact (x.modulusIndex+1).Prime]
      (h : Data.Valid j threshold x) (P G S : Tape) (_ : solid P) (_ : solid G) (_ : solid S)
      {D : Type} (pay : Series D) (_ : pay.count ≤ width) (z : x.Wide P G S f D),
      let hdr := InterchangeROMAddress.header f P G S
      let localWidth := width+(size hdr+1)^e
      ChartStep h P G S pay width (K x * mass (send hdr) (x.stageRows P G S f).count localWidth) z := by
  obtain ⟨e,he,K,hK,run⟩ := chart_step
  refine ⟨e,he,K,hK,?_⟩
  intro j threshold f width x nz prime h P G S p g s D pay hw z
  exact run (width:=width) (localWidth:=width+_) h P G S p g s pay (by omega) (by omega) z

end InterchangeROMRepair.Physical.Selected

end NearSquareRoot
end Computability
end OAI
