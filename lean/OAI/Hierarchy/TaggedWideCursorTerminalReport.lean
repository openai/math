import OAI.Hierarchy.TaggedWideRankedRows
import OAI.Hierarchy.TaggedWireReportedPath

namespace OAI
/-! # Transport the entire terminal report across cursor replay -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.PhysicalTerm
open LinearAlgebra.SpectralBooks ChordGraph
open AdaptiveProbe WireTelescope TaggedPrune Tagged ProtocolRAMEmit
open ProtocolRAM.Calendar ProtocolRAM.Calendar.FixedProtocolFormat WireTelescope.CalendarTape
open scoped Classical
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
variable {h d k w R M den : ℕ} {X : Type} (p : Equiv.Perm (Tagged.Row h))
local notation "U" => Widths (siteLast h d k+1)
local notation "Rpt" => Report p d k w R M den
local notation "bundle" => (u:U) × Rpt u

theorem report_bundle_transport {u u' : U} (r : Rpt u) (head : u=u') :
    (⟨u',FixedProtocolFormat.Report.transportLedger r head⟩ : bundle)=⟨u,r⟩ := by
  cases head
  rfl

theorem report_eq_of_bundle {u u' : U} {r : Rpt u} {r' : Rpt u'}
    (same : (⟨u,r⟩ : bundle)=⟨u',r'⟩) (head : u'=u) :
    r=FixedProtocolFormat.Report.transportLedger r' head := by
  cases head
  have ordinal : r=r' := eq_of_heq (Sigma.ext_iff.mp same).2
  cases ordinal
  rfl

variable {slots : Event→Slot X} {es : List Event} {startMem : X}
local notation "P" => Prefix slots es startMem
local notation "B" => (Prefix.start : P es startMem)
variable (width : ∀{tail x},P tail x→U)
    (report : ∀j : Path slots es startMem, Rpt (width (Prefix.finish B j)))
    (j : Path slots es startMem)
local notation "out" => cursorReport p width report (Prefix.histories B j)

theorem cursor_report_bundle :
    (⟨_,out⟩ : bundle)=⟨_,report j⟩ := by
  have sameWidth := (congrArg (Prefix.atWidth @width)
    (Prefix.terminal_history B (Prefix.histories B j))).symm
  apply (report_bundle_transport p (report ((Prefix.histories B).symm (Prefix.histories B j))) sameWidth).trans
  exact congrArg (fun t : Path slots es startMem=>(⟨_,report t⟩ : bundle))
    ((Prefix.histories B).symm_apply_apply j)

namespace CalendarTerms.RankedRows
variable {F : Type} [Field F] {L groups ports lanes m n view:ℕ} {key : Fin L ↪ ℕ×ℕ} {D : Type}
local notation "Rows" => RankedRows (F:=F) key D groups ports lanes w m n view
local notation "table" r:arg => (⟨(r).edges,(r).rows⟩ : CalendarTerms.RowBoard)

/-- The state space is already the width of the actual last cursor. The
cut installation and its private numbering move with the report row table. -/
theorem move_report {u : U} {one two : Rpt u} (same : one=two) (rowEq : table one=table two)
    (chosen : Rows (table two)) (test : (a : Rpt u)→Rows (table a)→Prop)
    (valid : test two chosen) : test one (move rowEq chosen) := by
  cases same
  exact valid

end CalendarTerms.RankedRows
end Hierarchy.ProbeStage.CoreBoard.PhysicalTerm
end

end OAI
