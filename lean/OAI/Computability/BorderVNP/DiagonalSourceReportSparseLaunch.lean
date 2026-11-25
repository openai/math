import OAI.Computability.BorderVNP.DiagonalReturnedSparseFields
import OAI.Computability.BorderVNP.DiagonalSourceReportInputs

/-! # Compact sparse cells launched from the actual selected report inverse -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM DiagonalTallyCellReports

/-- The actual report return, decoded in the received source's row order. -/
theorem ReportArgumentCut.assignment {w n : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {mem : Memory w}
    {s : Bank w} {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    {ret : Returns prepareCellReports pub mac s mem} {rows : ReportAssignments cs}
    (cut : ReportArgumentCut ret rows q n) :
    (assignedReportReturnEquiv cut.seed mac s).symm ret=rows := by
  change reportAssignmentEquiv cs ((reportReturnEquiv cut.seed mac s).symm ret)=rows
  rw [←cut.chosen,Equiv.apply_symm_apply]

end RoutingISA.Evaluator.SignedPrep

namespace Diagonal.ExternalSew.Fragments

open VPVNP.BurstRAM Crossing Packing Packing.Directory Packing.CellAddresses Packing.Inherited
open RoutingISA RoutingISA.Evaluator RoutingISA.SparseExterior RoutingISA.CompactMachine
open Cube.Physical DiagonalTallyCellReports DiagonalTallyAllocation CellSparse
open scoped Classical
set_option maxHeartbeats 1400000

variable {D R r literalWidth link V g edges entries desc w : ℕ}
    (arena : SignedTaskArena.Layout) (N : Network D (FreeBlock R V) (fun _ => g))
    (cell : N.Site → Fin arena.fragments.cells) (edgeID : N.Edge ↪ Fin edges)
    (head base : ℕ) (old : Memory w) (actual : Fin arena.fragments.cells → Memory w)
    (hg : 0<g) (room : r*(2*literalWidth+R*link) ≤ V*g) (pp lp : ℕ → ℕ × ℕ)
    (place : LivePlacement N cell edgeID finProdFinEquiv.toEmbedding lp)
    (input : FreePort R r literalWidth → Bool) (ends : Bool → LiveBit N cell → Bool)
    {description : ℕ} {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    {pub : Arg → Word w} {m : Memory w} {mac : TeamOpcode.Macros w 8} {s : Bank w}
    (banks : CellBanks.Layout) (alloc : ReportAllocation arena.before arena.after banks l cs q)
    (header : CellPacket.WordsAt (readings m) l.headers (cs.flatMap ReportCell.headerWords))
    (run : Returns prepareCellReports pub mac s m)
local notation3 (prettyPrint := false) "mem" => readings run.val.2.2
local notation3 (prettyPrint := false) "f" => FragmentRows.Layout.fromFrame head (readings run.val.2.2)
local notation3 (prettyPrint := false) "supplied" => fun n : ℕ => mem ((f).supplied+n)
local notation3 (prettyPrint := false) "bank" => fillFree hg room input (fun _ => false)
local notation3 (prettyPrint := false) "data" => endData N cell edgeID finProdFinEquiv.toEmbedding bank ends
local notation3 (prettyPrint := false) "dir" => freeDirectory R r literalWidth link V g entries desc
local notation3 (prettyPrint := false) "publication" =>
  readings (Directory.ISA.publish old head base (Packing.Directory.Layout.directory dir pp lp))
local notation3 (prettyPrint := false) "chosen" => (assignedReportReturnEquiv seed mac s).symm run

open RoutingISA.FragmentRows
set_option maxRecDepth 7200


open RoutingISA.Evaluator.SignedPrep

/-- At the original control return, the source-ordered report cut supplies
both the physical inputs and the proposal equality of the sparse launcher. -/
noncomputable abbrev returnedSparseFieldsOnCut
    (src : ReportAssignments cs) (cut : ReportArgumentCut run src q description)
    (fits : (f).Fits w mem) (hCells : arena.fragments.cells=(f).cells)
    (e : SparseEmission arena f run.val.2.2 fits hCells) (team offsets ctl live ports : ℕ) :=
  returned_sparse_fields (entries:=entries) (desc:=desc) arena N cell edgeID head base old actual hg room pp lp place input ends banks alloc cut.seed header run
    fits hCells e (team:=team) (offsets:=offsets) (ctl:=ctl) (live:=live) (ports:=ports) src cut.assignment

end Diagonal.ExternalSew.Fragments

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator SignedPrep Routing
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

set_option maxHeartbeats 170000
set_option maxRecDepth 6500


/-- On every jointly supported candidate, use the actual chronological control
and report return to provide an original source-ordered launcher cut; every
digit used by the subsequent compact field is this proposal's digit. -/
theorem PreparationFrame.sourceEquiv_sparse_proposal (agree : F.SourceAgreement fixed S B)
    (q : {v : Declared ar owners decl // S.pins v.val}) (reports : S.actual q.val.val) (u : Fin (R+1)) :
    let full := (F.sourceEquiv fixed S B agree).symm ⟨q,reports⟩
    let raw := declaredWords ar owners decl q.val
    let a : Matching ar owners decl raw.val := ⟨q.val.val,q.val.property,rfl⟩
    let checked : Subtype (B raw).pins := ⟨a,(agree.pins raw a).mpr q.property⟩
    let data := (B raw).localRows checked u
    let v := (visitsEquiv id (pub full.1 u) (mac full.1 u) (reg full.1 u) (mem full.1 u)).symm (full.2 u)
    ∃ cut : ReportArgumentCut v.reports (reports u) data.cursor data.description,
      (assignedReportReturnEquiv cut.seed (mac full.1 u) v.controls.val.2.1).symm v.reports=reports u := by
  intro full raw a checked data v
  obtain ⟨cut⟩ := F.sourceEquiv_report_cut fixed S B agree q reports u
  exact ⟨cut,cut.assignment⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
