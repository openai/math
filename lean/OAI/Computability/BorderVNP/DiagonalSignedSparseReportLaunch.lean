import OAI.Computability.BorderVNP.DiagonalPublishedSparseCell
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomStride

/-! # A returned signed report launches its authentic compact native cell -/

namespace OAI
namespace Computability
namespace BorderVNP

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
    (seed : PreparedReportInput pub m cs q description)
    (header : CellPacket.WordsAt (readings m) l.headers (cs.flatMap ReportCell.headerWords))
    (run : Returns prepareCellReports pub mac s m) (i : Fin cs.length) (c : Fin arena.fragments.cells)
local notation3 (prettyPrint := false) "mem" => readings run.val.2.2
local notation3 (prettyPrint := false) "f" => FragmentRows.Layout.fromFrame head (readings run.val.2.2)
local notation3 (prettyPrint := false) "supplied" => fun n : ℕ => mem ((f).supplied+n)
local notation3 (prettyPrint := false) "bank" => fillFree hg room input (fun _ => false)
local notation3 (prettyPrint := false) "data" => endData N cell edgeID finProdFinEquiv.toEmbedding bank ends
local notation3 (prettyPrint := false) "dir" => freeDirectory R r literalWidth link V g entries desc
local notation3 (prettyPrint := false) "publication" =>
  readings (Directory.ISA.publish old head base (Packing.Directory.Layout.directory dir pp lp))
local notation3 (prettyPrint := false) "chosen" => (assignedReportReturnEquiv seed mac s).symm run
local notation3 (prettyPrint := false) "report" => (chosen).val[i.val]'(i.isLt.trans_eq (chosen).length.symm)
local notation3 (prettyPrint := false) "ss" => spans ((f).stream mem) data c.val
local notation3 (prettyPrint := false) "field" => (⟨(report).supplied,ss,(report).bits⟩ : SparseExterior.Field)

include place alloc header in
/-- From an arbitrary scanner return, take the global row which its real
header names. The published seven-word directory and scattered native
source words determine its sparse spans. The clocked private packet bound
pays its physical byte window. Its restored value includes every logical
lane of the original end assignment, followed by exactly this report. -/
theorem exists_returned_sparse_cell (fits : (f).Fits w mem) (hCells : arena.fragments.cells=(f).cells)
    (global : c.val=(report).number) (executing : actual c=run.val.2.2)
    (address : mem ((f).host.cells+2*c.val+1)=(report).external) (sup : supplied c.val=(report).supplied)
    (bankStart : banks.bankStart=arena.cube.cellBank) (stride : banks.stride=arena.cube.cellStride)
    (rows : CableRows N cell edgeID finProdFinEquiv.toEmbedding (f).host mem)
    (counts : ∀ v : Fin arena.fragments.cells, supplied v.val=suppliedSize N cell v)
    (privateAfter : ∀ j : Fin entries, supplied (pp j.val).1≤(pp j.val).2)
    (bases : ∀ v : Fin arena.fragments.cells, mem ((f).host.cells+2*v.val+1)=arena.cube.cellBank+v.val*arena.cube.cellStride)
    (read : SourceWords N cell edgeID finProdFinEquiv.toEmbedding hg room lp arena.cube.cellBank arena.cube.cellStride
      input ends (fun v => readings (actual v)))
    (original : readings old (head+8)=base) (apart : head+9<base)
    (len : ((dir).directory pp lp).length<2^w)
    (words : ∀ j : Fin ((dir).directory pp lp).length, ∀ x∈((dir).directory pp lp)[j.val].words, x<2^w)
    (ptr : mem (head+8)=publication (head+8)) (num : mem (head+9)=publication (head+9))
    (kept : ∀ addr, base≤addr → addr<base+7*((dir).directory pp lp).length → mem addr=publication addr)
    {n p : ℕ} (packet : CellSparse.Directory) (hn : 1≤n) (hw : 0<w) (hw' : w≤n)
    (window : arena.p.scratchStride=SignedTaskArena.scratchWindow n)
    (paid : (CompactFrame.pack w (Packet.input packet p (field).bytes)).length≤TeamScales.width n (1/2)) :
    ∃ v : FragmentRows.SparseCell arena f run.val.2.2 data i.val, v.number=c ∧ v.tail=(report).bits ∧
      (v.owned (fit:=fits) (cells:=hCells)).field.values=
        List.ofFn (Placement.endSupply N cell c edgeID finProdFinEquiv.toEmbedding bank ends)++(report).bits := by
  have stream := published_report_spans (entries:=entries) (desc:=desc) N cell edgeID head base old run.val.2.2
    actual hg room pp lp arena.cube.cellBank arena.cube.cellStride place input ends c (report).bits rows counts
    privateAfter bases read original apart len words ptr num kept
  have order : SparseExterior.Ordered (report).supplied 0 ss := sup ▸ stream.1
  have sources : ∀ span ∈ ss, span.Reads run.val.2.2 := executing ▸ stream.2.1
  have occupied := (SignedTaskArena.windows_of_packet packet field hn hw hw' paid).1
  have extent : (SparseExterior.encode (report).supplied (report).bits 0 ss).length ≤ arena.fragments.stride :=
    occupied.trans_eq window.symm
  let v := sparseCellOfReportReturn arena banks f data alloc seed header run i c global address sup bankStart stride
    order sources extent
  refine ⟨v,rfl,rfl,?_⟩
  let pos : Fin (chosen).val.length := ⟨i.val,i.isLt.trans_eq (chosen).length.symm⟩
  let cursor := ((chosen).val.take i.val).foldl (fun a c => c.after a) q
  have reportRead : (report).BindingReadback cursor mem := returned_report_binding alloc seed run pos
  exact owned_report_values (entries:=entries) (desc:=desc) arena N cell edgeID finProdFinEquiv.toEmbedding head base old run.val.2.2
    fits hCells rows hg room pp lp place counts privateAfter input ends v report cursor reportRead global alloc.widths.symm
    address sup original apart len words ptr num kept

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
