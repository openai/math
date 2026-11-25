import OAI.Computability.BorderVNP.FragmentRowsSparseLaunch
import OAI.Computability.BorderVNP.DiagonalNativeReportBindingReadback

/-! # Physical signed report rows in the global call directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA FragmentRows SparseExterior DiagonalTallyAllocation Diagonal.ExternalSew.Fragments

/-- The signed scanner has already written the exact bit tail and tail width.
Appending these returned words to the routed physical spans constructs the
live row consumed by the sparse exterior encoder. -/
noncomputable def ReportCell.BindingReadback.sparseRow {w i : ℕ} {orig : Memory w} {l : ReportLayout}
    {report : ReportCell l} {cursor : ReportCursor} (readback : report.BindingReadback cursor (readings orig))
    (a : SignedTaskArena.Layout) (f : FragmentRows.Layout) (data : ℕ → ℕ → Bool)
    (cell : report.number < a.fragments.cells) (sameWidth : a.before.tailWidths=l.tailWidths)
    (bank : readings orig (f.host.cells+2*report.number+1)=report.external)
    (placed : report.external=a.cube.cellBank+report.number*a.cube.cellStride)
    (width : readings orig (f.supplied+report.number)=report.supplied)
    (full : report.supplied+report.tailWidth≤a.cube.cellStride)
    (six : readings orig (a.before.six+6*i)=report.number ∧ readings orig (a.before.six+6*i+2)=report.supplied)
    (ordered : Ordered report.supplied 0 (spans (f.stream (readings orig)) data report.number))
    (sources : ∀ z ∈ spans (f.stream (readings orig)) data report.number, z.Reads orig)
    (extent : (encode report.supplied report.bits 0 (spans (f.stream (readings orig)) data report.number)).length≤a.fragments.stride) :
    SparseCell a f orig data i := by
  refine ⟨⟨report.number,cell⟩,report.bits,bank.trans placed,?_,six.1,six.2.trans width.symm,?_,?_,sources,?_,?_⟩
  · simpa only [width,ReportCell.bits_length] using full
  · simpa only [sameWidth,ReportCell.bits_length] using readback.width
  · simpa only [width] using ordered
  · intro j hj
    change readings orig (readings orig (f.host.cells+2*report.number+1)+readings orig (f.supplied+report.number)+j) = _
    rw [bank,width]
    have read := readback.bits (⟨j,by simpa using hj⟩ : Fin (report.bits.map Bool.toNat).length)
    simpa only [List.getElem_map] using read
  · simpa only [width] using extent

end DiagonalTallyCellReports

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM SignedTaskArena SparseExterior TypedTaskBuilder
open Diagonal.ExternalSew.Fragments

variable {w : ℕ} {a : SignedTaskArena.Layout} {f : FragmentRows.Layout} {orig : Memory w}
    {fit : f.Fits w (readings orig)} {cells : a.fragments.cells=f.cells}
    (e : SparseEmission a f orig fit cells) {team frame offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool}

set_option quotPrecheck false
local notation "R" => a.controlRows team frame offsets ctl live ports
local notation "num" => (R).before (readings e.output) (R).cells
local notation "idx" => globalCell (R).toLayout (readings e.output)

variable (rows : (i : Fin ((a.controlRows team frame offsets ctl live ports).toLayout.before (readings e.output) a.cube.cells)) →
    SparseCell a f orig data i.val)
    (ownerOrder : ∀ i, (rows i).number.val=globalCell (a.controlRows team frame offsets ctl live ports).toLayout (readings e.output) i.val)

/-- Label the actual compact received rows by their global cells. Values
outside this team's owner scan never enter a call on that processor. -/
noncomputable def SparseEmission.globalCells : ℕ → SparseExterior.Owned :=
  Function.extend (fun i : Fin num => idx i.val) (fun i => (rows i).owned (fit:=fit) (cells:=cells))
    (fun c => ⟨c,0,0,⟨0,[],[]⟩⟩)

/-- Looking up a compact task by its genuine global cell recovers its physical sparse row. -/
theorem SparseEmission.globalCells_at (i : Fin num) :
    e.globalCells (team:=team) (frame:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live) (ports:=ports)
      rows (idx i.val) = (rows i).owned (fit:=fit) (cells:=cells) := by
  apply Function.Injective.extend_apply
  apply StrictMono.injective
  intro j k lt
  exact global_strict (R).toLayout (readings e.output) lt k.isLt

local notation "field" => SparseEmission.globalCells (team:=team) (frame:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live)
  (ports:=ports) e rows

include ownerOrder in
/-- The actual bucket bounds, dense bank and received report imply all five
per-cell word/area obligations of the signed argument producer at each
global cell assigned to this team, including on nonpassing reports. -/
theorem SparseEmission.globalCells_bounds (c : ℕ) (hc : c < (R).cells) (belongs : (R).owner (readings e.output) c=(R).team) :
    let z := field c
    z.global=c ∧ z.field.bytes.length≤a.fragments.stride ∧ z.first+z.field.spans.length≤a.fragments.capacity ∧
      z.dense+z.field.width+z.field.tail.length≤a.fragments.start ∧
      ∀ r ∈ z.field.spans, r.source+r.bits.length≤a.fragments.start := by
  let i := (R).before (readings e.output) c
  have hi : i<num := (R).toLayout.before_strict (readings e.output) hc belongs
  let j : Fin num := ⟨i,hi⟩
  have atCell : idx j.val=c := global_at (R).toLayout (readings e.output) hc belongs
  have atRow := e.globalCells_at (team:=team) (frame:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live) (ports:=ports) rows j
  rw [atCell] at atRow
  simp only [atRow]
  let row := rows j
  have src := owned_bank_bounds a f (readings orig) row.number data row.tail row.bank row.full row.ordered
  exact ⟨(ownerOrder j).trans atCell,row.extent,e.triples_bound data row.number,src.2,src.1⟩

include ownerOrder in
/-- At every compact task the sparse writer starts on the real post-patch
memory with precisely the record indexed by the global call directory. -/
theorem SparseEmission.globalCells_initial {Site : Type} {u v k : ℕ}
    (patch : SparsePatch (w:=w) Site (a.controlRows team frame offsets ctl live ports) (readings e.output))
    (placement : a.SparsePlacement frame ctl) (geo : SparseGeometry a f offsets ctl)
    (high : a.endAddress w u v k<2^w) :
    ∀ i < num, (field (idx i)).Initial (batchLayout a frame ctl num) i patch.memory := by
  intro i hi
  let j : Fin num := ⟨i,hi⟩
  change (field (idx j.val)).Initial _ _ _
  rw [e.globalCells_at (team:=team) (frame:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live) (ports:=ports) rows j]
  exact e.initial_in_patch patch placement geo high hi (rows j) (ownerOrder j)

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
