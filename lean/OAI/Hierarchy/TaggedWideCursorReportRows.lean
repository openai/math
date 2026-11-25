import OAI.Hierarchy.TaggedWireCursorTerm

namespace OAI
/-! # Original report row numbering on the replayed signed calendar cursor -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.PhysicalTerm
open LinearAlgebra.SpectralBooks ChordGraph
open AdaptiveProbe WireTelescope TaggedPrune Tagged ProtocolRAMEmit
open ProtocolRAM.Calendar WireTelescope.CalendarTape
open scoped Classical
set_option quotPrecheck false

variable {h d k w R M den : ℕ} {X : Type} (p : Equiv.Perm (Tagged.Row h))
    {slots : Event→Slot X} {es : List Event} {startMem : X}
private abbrev reportStart (slots : Event → Slot X) (es : List Event) (startMem : X) :
    WireTelescope.CalendarTape.Prefix slots es startMem es startMem := .start

variable (width : ∀{tail x}, WireTelescope.CalendarTape.Prefix slots es startMem tail x → Widths (siteLast h d k+1))
    (report : ∀j : Path slots es startMem, Report p d k w R M den
      (width (Prefix.finish (reportStart slots es startMem) j)))
    (j : Path slots es startMem)
local notation "B" => reportStart slots es startMem
local notation "out" => cursorReport p width report (Prefix.histories B j)

/-- The original numbered RAM rows with the geometry constructed by their ledger. -/
abbrev RowGeometry (h d k w R M den : ℕ) :=
  (n : ℕ) × (rows : Fin n → ProtocolRAMEmit.Row) ×
    ProtocolRAMEmit.Geometry (boardLayout h d k w R) M den rows

def reportGeometry {U} (r : Report p d k w R M den U) : RowGeometry h d k w R M den :=
  ⟨r.edges,r.rows,r.geometry⟩

/-- Replaying an original path changes the proof naming the terminal width.
The entire ranked physical row table and its geometry still come from the same report. -/
theorem cursor_report_geometry :
    reportGeometry p out=reportGeometry p (report j) := by
  change (fun j : Path slots es startMem => reportGeometry p (report j))
    ((Prefix.histories B).symm (Prefix.histories B j))=_
  rw [Equiv.symm_apply_apply]

def cursor_report_transport (P₀ : RowGeometry h d k w R M den → Sort*)
    (facts : P₀ (reportGeometry p (report j))) : P₀ (reportGeometry p out) :=
  (cursor_report_geometry p width report j).symm ▸ facts

/-- Row arity and all physical row words are jointly invariant under cursor replay. -/
theorem cursor_report_rows :
    (⟨(out).edges,(out).rows⟩ : (n : ℕ)×(Fin n→ProtocolRAMEmit.Row)) =
      ⟨(report j).edges,(report j).rows⟩ := by
  change (fun j : Path slots es startMem =>
    (⟨(report j).edges,(report j).rows⟩ : (n : ℕ)×(Fin n→ProtocolRAMEmit.Row)))
    ((Prefix.histories B).symm (Prefix.histories B j)) = _
  rw [Equiv.symm_apply_apply]

theorem cursor_report_edges : (out).edges=(report j).edges :=
  congrArg Sigma.fst (cursor_report_rows p width report j)

theorem cursor_report_row (e : Fin (out).edges) :
    (out).rows e=(report j).rows (e.cast (cursor_report_edges p width report j)) := by
  have congruent {a b : (n:ℕ)×(Fin n→ProtocolRAMEmit.Row)} (eq : a=b)
      (e : Fin a.1) : a.2 e=b.2 (e.cast (congrArg Sigma.fst eq)) := by
    cases eq
    rfl
  exact congruent (cursor_report_rows p width report j) e

end Hierarchy.ProbeStage.CoreBoard.PhysicalTerm

end
end OAI
