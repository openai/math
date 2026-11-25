import OAI.Computability.BorderVNP.RoutingISASignedPrepFrame

/-! # Report rows on a fixed routed source assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open DiagonalTallyCellReports BorderVNP.Cube Physical Physical.NativeAssignments

/-- The physical layout and all immutable fields of the ordered received cells
match the source cells. Sampled gadget digits and marked use flags are erased. -/
structure SameReportCells {l k : ReportLayout} (cs : List (ReportCell l)) (ds : List (ReportCell k)) : Prop where
  /-- Absolute operands and digit dimensions agree for this team. -/
  layout : l=k
  /-- Clearing the guess fields leaves the same original ordered cell list. -/
  rows : (layout ▸ eraseReportBits cs)=eraseReportBits ds

/-- Reindex physically sampled reports on identical immutable inputs. -/
def SameReportCells.equiv {l k : ReportLayout} {cs : List (ReportCell l)} {ds : List (ReportCell k)}
    (same : SameReportCells cs ds) : ReportAssignments cs ≃ ReportAssignments ds := by
  obtain ⟨eq,rows⟩ := same
  subst k
  change eraseReportBits cs=eraseReportBits ds at rows
  exact Equiv.subtypeEquivRight fun _ => by rw [rows]

/-- No chronological count or marked-use bit changes in the reindexing. -/
theorem SameReportCells.equiv_bits {l k : ReportLayout} {cs : List (ReportCell l)} {ds : List (ReportCell k)}
    (same : SameReportCells cs ds) (a : ReportAssignments cs) :
    reportBits ((same.equiv a).val)=reportBits a.val := by
  cases same with
  | mk eq _ => subst k; rfl

variable {R : ℕ} (ar : CubeArena.Layout)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))

/-- The physical zero pins and report cells belonging to one source path, fixed
before any subtotal claim or observed native history is chosen. -/
structure SourceReports where
  /-- Zero pins at the unfilled host ports of the selected cube. -/
  pins : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners → Prop
  /-- The reporting team's field widths and its physical input addresses. -/
  layout : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners → Fin (R+1) → ReportLayout
  /-- The received cells in the source's ordinal order. -/
  cells : ∀ q u, List (ReportCell (layout q u))

variable {ar owners} (S : SourceReports ar owners)

/-- All independently sampled reports at the physical source assignment. -/
abbrev SourceReports.actual (q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners) :=
  (u : Fin (R+1)) → ReportAssignments (S.cells q u)

end RoutingISA.Evaluator.SignedPrep

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally DiagonalTallyCellReports

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w} {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ}
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
    (S : SourceReports ar owners) (F : PreparationFrame G L ar decl header pin pub mac reg mem)
    (B : F.Builders fixed id owners)

set_option quotPrecheck false in
local notation "guard" => fun raw => (B raw).pins

/-- Identify the physical host checks and actual immutable per-team reporting rows
with the same source path even when the claimed subtotal fields vary. -/
structure PreparationFrame.SourceAgreement : Prop where
  /-- The true native free-port guard agrees with the source zero pins. -/
  pins : ∀ raw : SharedWords ar decl, ∀ q : Matching ar owners decl raw.val, (B raw).pins q ↔ S.pins q.val
  /-- The physical cells and their source counterparts differ only in their seed guesses. -/
  cells : ∀ (raw : SharedWords ar decl) (q : Subtype ((B raw).pins)) u,
    SameReportCells ((B raw).localRows q u).cells (S.cells q.val.val u)

/-- At this genuine header the full signed preparations are indexed by the
source's compatible pinned cube paths and their original per-team report rows. -/
noncomputable def PreparationFrame.sourceEquiv (agree : F.SourceAgreement fixed S B) :
    (Σ x : HeaderExterior L header, (u : Fin (R+1)) → Returns
      (prepareExpansion epochPlacement (scheduleGroups ar.n (selectorWidth ar.n ar.K ar.h))
        (signedInputs id (TeamRows.ownedGroups ar.n ar.b ar.h ar.K ar.s))) (pub x u) (mac x u) (reg x u) (mem x u)) ≃
      Σ q : {v : Declared ar owners decl // S.pins v.val}, S.actual q.val.val := by
  let convert : PinnedDeclared ar owners decl guard ≃ {v : Declared ar owners decl // S.pins v.val} :=
    Equiv.subtypeEquivRight fun v => by
      let x := (sharedMatchingEquiv ar owners decl).symm v
      exact agree.pins x.1 x.2
  refine (F.returnEquiv fixed id owners B).trans (Equiv.sigmaCongr convert ?_)
  intro q
  let x := (pinnedMatchingEquiv ar owners decl guard).symm q
  exact Equiv.piCongrRight fun u => (agree.cells x.1 x.2 u).equiv

end TeamContraction

end BorderVNP
end Computability
end OAI
