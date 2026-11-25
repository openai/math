import OAI.Computability.BorderVNP.DiagonalSignedSparseReportLaunch
import OAI.Computability.BorderVNP.DiagonalSignedGlobalSparseLaunch

/-! # Compact signed sparse inputs on every actual returned report row -/

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

include place alloc header in
/-- The choices of honest sparse cells made on the *same* returned report memory
assemble into the actual globally indexed fields of the sparse argument writer.
The incoming rows may use every possible count digit and source-box bit. -/
theorem returned_sparse_fields (fits : (f).Fits w mem) (hCells : arena.fragments.cells=(f).cells)
    (e : SparseEmission arena f run.val.2.2 fits hCells) {team offsets ctl live ports : ℕ}
    (src : ReportAssignments cs) (returned : (assignedReportReturnEquiv seed mac s).symm run=src)
    (host : Fin cs.length → Fin arena.fragments.cells)
    (bankStart : banks.bankStart=arena.cube.cellBank) (stride : banks.stride=arena.cube.cellStride)
    (wiring : CableRows N cell edgeID finProdFinEquiv.toEmbedding (f).host mem)
    (counts : ∀ v : Fin arena.fragments.cells, supplied v.val=suppliedSize N cell v)
    (privateAfter : ∀ j : Fin entries, supplied (pp j.val).1≤(pp j.val).2)
    (bases : ∀ v : Fin arena.fragments.cells, mem ((f).host.cells+2*v.val+1)=arena.cube.cellBank+v.val*arena.cube.cellStride)
    (read : SourceWords N cell edgeID finProdFinEquiv.toEmbedding hg room lp arena.cube.cellBank arena.cube.cellStride
      input ends (fun v => readings (actual v)))
    (original : readings old (head+8)=base) (apart : head+9<base)
    (len : ((dir).directory pp lp).length<2^w)
    (words : ∀ j : Fin ((dir).directory pp lp).length, ∀ x∈((dir).directory pp lp)[j.val].words, x<2^w)
    (ptr : mem (head+8)=publication (head+8)) (total : mem (head+9)=publication (head+9))
    (kept : ∀ addr, base≤addr → addr<base+7*((dir).directory pp lp).length → mem addr=publication addr)
    {n : ℕ} (packet : Fin cs.length → CellSparse.Directory) (pw : Fin cs.length → ℕ)
    (hn : 1≤n) (hw : 0<w) (hw' : w≤n) (window : arena.p.scratchStride=SignedTaskArena.scratchWindow n) :
    let R := arena.controlRows team head offsets ctl live ports
    let count := R.toLayout.before (readings e.output) arena.cube.cells
    let proposed := fun i : Fin cs.length => src.val.get (Fin.cast src.length.symm i)
    ∀ (roster : count=cs.length),
    (∀ i : Fin count, (host (Fin.cast roster i)).val=RoutingISA.TypedTaskBuilder.globalCell R.toLayout (readings e.output) i.val) →
    (∀ i, let c := host i; let r := proposed i
      c.val=r.number ∧ actual c=run.val.2.2 ∧ mem ((f).host.cells+2*c.val+1)=r.external ∧ supplied c.val=r.supplied) →
    (∀ i, let c := host i; let rr := proposed i
      let field : SparseExterior.Field := ⟨rr.supplied,spans ((f).stream mem) data c.val,rr.bits⟩
      (CompactFrame.pack w (Packet.input (packet i) (pw i) field.bytes)).length≤TeamScales.width n (1/2)) →
    ∃ rows : (j : Fin count) → SparseCell arena f run.val.2.2 data j.val,
      (∀ j,(rows j).number=host (Fin.cast roster j) ∧ (rows j).tail=(proposed (Fin.cast roster j)).bits) ∧
      ∀ i : Fin cs.length, let c := host i
        ((e.globalCells (team:=team) (frame:=head) (offsets:=offsets) (ctl:=ctl) (live:=live) (ports:=ports)
          rows c.val).field).values=
            List.ofFn (Placement.endSupply N cell c edgeID finProdFinEquiv.toEmbedding bank ends)++(proposed i).bits := by
  intro R count proposed roster ownerOrder owned paid
  have all (i : Fin cs.length) :
      ∃ v : SparseCell arena f run.val.2.2 data i.val,
        v.number=host i ∧ v.tail=(proposed i).bits ∧
        (v.owned (fit:=fits) (cells:=hCells)).field.values=
          List.ofFn (Placement.endSupply N cell (host i) edgeID finProdFinEquiv.toEmbedding bank ends)++(proposed i).bits := by
    obtain ⟨key,executing,addr,supply⟩ := owned i
    have same : (chosen).val[i.val]'(i.isLt.trans_eq (chosen).length.symm)=proposed i := by cases returned; rfl
    exact same ▸ exists_returned_sparse_cell arena N cell edgeID head base old actual hg room pp lp place input ends banks
      alloc seed header run i (host i) fits hCells (same.symm ▸ key) executing (same.symm ▸ addr) (same.symm ▸ supply)
      bankStart stride wiring counts privateAfter bases read original apart len words ptr total kept (packet i) hn hw hw'
      window (same.symm ▸ paid i)
  let rows (j : Fin count) := (all (Fin.cast roster j)).choose
  refine ⟨rows,fun j => ⟨(all _).choose_spec.1,(all _).choose_spec.2.1⟩,?_⟩
  intro i c
  let j := Fin.cast roster.symm i
  have eq : Fin.cast roster j=i := Fin.ext rfl
  have here : c.val=RoutingISA.TypedTaskBuilder.globalCell R.toLayout (readings e.output) j.val :=
    (congrArg (fun t => (host t).val) eq.symm).trans (ownerOrder j)
  rw [here,e.globalCells_at (team:=team) (frame:=head) (offsets:=offsets) (ctl:=ctl) (live:=live) (ports:=ports) rows j]
  exact (all i).choose_spec.2.2

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
