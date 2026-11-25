import OAI.Computability.BorderVNP.DiagonalSignedGlobalSparseLaunch
import OAI.Computability.BorderVNP.DiagonalProducedArgumentCells
import OAI.Computability.BorderVNP.RoutingISASparseReportSources

/-! # The actual signed fragment rows in the native report and cell clock -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM SparseExterior TypedTaskBuilder Diagonal.ExternalSew.Fragments

variable {w : ℕ} {a : SignedTaskArena.Layout} {f : FragmentRows.Layout} {orig : Memory w}
    {fit : f.Fits w (readings orig)} {cells : a.fragments.cells=f.cells}
    (e : SparseEmission a f orig fit cells) {team frame offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool}
set_option quotPrecheck false
local notation "R" => a.controlRows team frame offsets ctl live ports
local notation "raw" => readings e.output
local notation "num" => (R).before (readings e.output) (R).cells
local notation "idx" => globalCell (R).toLayout (readings e.output)
variable (rows : (i : Fin ((a.controlRows team frame offsets ctl live ports).toLayout.before (readings e.output) a.cube.cells)) →
    SparseCell a f orig data i.val)
    (ownerOrder : ∀ i, (rows i).number.val=globalCell (a.controlRows team frame offsets ctl live ports).toLayout (readings e.output) i.val)
local notation "owned" => e.globalCells (team:=team) (frame:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live) (ports:=ports) rows

include ownerOrder in
/-- Read the occupied source stream, packet width, sorted intervals and sampled tail on the
unique compact row of a global cell. The tail can contain any guess that reached the writer. -/
theorem SparseEmission.reportFields (length : Fin a.cube.cells → ℕ)
    (counts : ∀ i, (rows i).tail.length=length (rows i).number)
    (c : Fin a.cube.cells) (mine : (R).owner raw c.val=(R).team) :
    let z := (owned c.val).field
    z.spans=spans (f.stream (readings orig)) data c.val ∧ Ordered z.width 0 z.spans ∧ z.width<2^w ∧ z.tail.length=length c := by
  let i : Fin num := ⟨(R).before raw c.val,(R).toLayout.before_strict raw c.isLt mine⟩
  have found : idx i.val=c.val := global_at (R).toLayout raw c.isLt mine
  have number : (rows i).number=c := Fin.ext ((ownerOrder i).trans found)
  have cellRow := e.globalCells_at (team:=team) (frame:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live) (ports:=ports) rows i
  rw [found] at cellRow
  dsimp only
  rw [cellRow]
  refine ⟨?_,(rows i).ordered,((orig (f.supplied+(rows i).number.val)).isLt),?_⟩
  · change spans _ _ (rows i).number.val=_
    rw [number]
  · exact (counts i).trans (congrArg length number)

end RoutingISA.FragmentRows

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube Cube.Physical Cube.TeamRowClock Cube.TeamRowSources
open Crossing Packing.CellAddresses Packing.Directory DiagonalTallyCellReports
open Diagonal.ExternalSew.Fragments CellPacket CellSparse CellSparse.Packet CellSparse.Packet.Source
open CellPacketGeometry FragmentRows TypedTaskBuilder CellDispatch

variable {Site E I P A : Type} [Fintype P] [Fintype A] {w n : ℕ}
    {arena : SignedTaskArena.Layout} {f : FragmentRows.Layout} {orig : Memory w}
    {fit : f.Fits w (readings orig)} {ncells : arena.fragments.cells=f.cells}
    (e : SparseEmission arena f orig fit ncells) {team frame offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool}
    (rows : (i : Fin ((arena.controlRows team frame offsets ctl live ports).toLayout.before (readings e.output) arena.cube.cells)) →
       SparseCell arena f orig data i.val)
    (ownerOrder : ∀ i, (rows i).number.val=globalCell (arena.controlRows team frame offsets ctl live ports).toLayout (readings e.output) i.val)
    (pub : Arg → Word w) (built : Memory w)
    (places : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List Record)
set_option quotPrecheck false
local notation "a" => arena.cube
local notation "rows₀" => arena.controlRows team frame offsets ctl live ports
local notation "mem" => readings e.output
local notation "bank" => readings orig
local notation "cells" => e.globalCells (team:=team) (frame:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live) (ports:=ports) rows

variable {p d R H B description : ℕ}
    (D : LengthDeclaration arena.cube.n arena.cube.header.d)
    (label : Fin arena.cube.cells → Label (arena.cube.n+1) arena.cube.header.d)
    (recv : A → Fin arena.cube.cells) (incoming : A → ℕ) (assigned : ℕ → ℕ)
local notation "owner" => scheduledCellOwner arena.cube D label assigned

include ownerOrder in
set_option maxHeartbeats 1800000 in
/-- The returning fragment emitter and actual seven-word sparse producer supply all
cell counts, clocks' indexed source arrays, report widths and sorted spans. The
remaining inputs are the selected network's crossing and delivery bounds, its
public count fields, and the native scanner's occupied binding and bundle rows. -/
noncomputable def SparseReportSources.ofEmitted
    (src : SparseCallInput pub built) (roster : ProducedRoster arena rows₀ mem places geom extra src)
    (fp : (pub 0).val=frame) (image : readings built=(rows₀).toLayout.published mem)
    (ownedRows : src.owned=fun j => cells (globalCell (rows₀).toLayout mem j))
    (typed : src.tasks=fun j => (SparseExterior.supplementalRow rows₀ mem src.layout cells places geom extra j).typed)
    {z ns ne np nc : ℕ} {bits : P → ℕ} (N : Network z P bits) (host : N.Site → Fin arena.cube.cells)
    (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin np) (ord : N.CrossingEdge host ≃ Fin nc)
    (cables : CableRows N host edge port f.host bank)
    (located : RowLocations ((List.range f.count).map (f.row bank)) (Fin.val : Fin arena.cube.cells → ℕ) recv incoming)
    (pairBound : ∀ pair, load (cablePair ord (crossSrc N host) (crossDst N host) label)
      (crossWidth N host ∘ ord.symm) pair ≤ arena.cube.header.blocks*(arena.cube.h*arena.cube.b))
    (template : LiveWords.Template E I Site ns (arena.cube.cells+1)) (site : Fin ns → Fin (arena.cube.cells+1)) (arg : E → ℕ) (emit : Fin ns → I → ℕ)
    (shape : TypedBatch.SourceFootprint (fun c => places c.val) (template.directory site arg emit))
    (pubRoom : (arena.cube.cells+1)+template.atoms.length+(arena.cube.cells+1) ≤ 2^p)
    (descRoom : (arena.cube.cells+1)+(Schema.coords template.chunkLabels.length).length+(arena.cube.cells+1) ≤ 2^d)
    (L : ReportLayout) (rs : Fin arena.cube.cells → ReportCell L) (cursor : Fin arena.cube.cells → LocalReportCursor)
    (base : Fin arena.cube.cells → ℕ) (source : Fin arena.cube.cells → ℕ → ℕ)
    (rowTail : ∀ j, (rows j).tail.length=(rs (rows j).number).tailWidth)
    (counts : ∀ c : Fin arena.cube.cells, (places c.val).reports.length=L.gadgets)
    (digits : ∀ c : Fin arena.cube.cells, ∀ g ∈ (places c.val).reports, g.length=L.countWidth)
    (hidden : BitDelivery (fun j : (c : Fin arena.cube.cells) × Fin ((places c.val).boxes.filterMap Sum.getRight?).length => j.1)
      (fun _ => description) recv incoming)
    (sent : BitDelivery (fun j : (c : Fin arena.cube.cells) × Fin (rs c).bundles.length => j.1) (fun _ => description) recv incoming)
    (body : ∀ c < (rows₀).cells, (rows₀).owner mem c=(rows₀).team → ∀ j,
      (places c).headerWidth+(boxBody ((places c).factors j)).length ≤ description)
    (owners : ∀ c : Fin arena.cube.cells, (rows₀).owner mem c.val=owner c)
    (bind : ∀ c, owner c=team → extra c.val=bindingRows (rs c).bundles (cursor c))
    (bundles : ∀ c, owner c=team → bundleInputs w L description (rs c).bundles (cursor c) (base c) (source c))
    (marked : ((c : {c : Fin arena.cube.cells // owner c=team}) × UsePositions (rs c.val).bundles) ↪
      Diagonal.CellEntries.PowerSlot (Fin R) (Fin H) B) :
    SparseReportSources Site E I P a D label recv incoming assigned team description p d R H B src f bank rows₀ mem := by
  have reads (c : Fin arena.cube.cells) (hc : owner c=team) := e.reportFields rows ownerOrder (fun j => (rs j).tailWidth) rowTail c
    ((owners c).trans hc)
  have ownerTable := roster.compressed pub built arena rows₀ mem places geom extra fp image rfl le_rfl
  have countFit : src.layout.count=(rows₀).before mem (rows₀).cells := by rw [roster.layout]; exact roster.count
  exact ⟨z,bits,N,host,ne,np,nc,edge,port,ord,cables,located,pairBound,cells,places,geom,extra,rfl,rfl,roster.count,countFit,
    data,fun c h => (reads c h).1,fun c h => (reads c h).2.1,fun c h => (reads c h).2.2.1,
    ns,template,site,arg,emit,shape,pubRoom,descRoom,L,rs,cursor,base,source,counts,digits,fun c h => (reads c h).2.2.2,
    hidden,sent,congrArg CellDispatch.Frame.count ownerTable.frame,body,owners,bind,bundles,marked,ownedRows,typed⟩

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
