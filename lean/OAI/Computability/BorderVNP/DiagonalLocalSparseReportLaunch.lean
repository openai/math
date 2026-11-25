import OAI.Computability.BorderVNP.DiagonalSparseReportDelivery
import OAI.Computability.BorderVNP.DiagonalSparsePreparedReports

/-! # The sparse and report clocks on one actual native report proposal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube Cube.Physical Cube.TeamRowClock Cube.TeamRowSources
open Crossing Packing.CellAddresses Packing.Directory DiagonalTallyCellReports
open Diagonal.ExternalSew.Fragments CellPacket CellSparse CellSparse.Packet CellSparse.Packet.Source
open CellPacketGeometry FragmentRows TypedTaskBuilder CellDispatch
open Packing.BundleDirectory DiagonalTallyCellReports.ReportDirectory

variable {E I P A : Type} [Fintype P] [Fintype A] {w n : ℕ}
    {arena : SignedTaskArena.Layout} {f : FragmentRows.Layout} {orig : Memory w}
    {fit : f.Fits w (readings orig)} {ncells : arena.fragments.cells=f.cells}
    (e : SparseEmission arena f orig fit ncells) {r : ℕ} (u : Fin (r+1)) {frame offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool}
    (rows : (i : Fin ((arena.controlRows u.val frame offsets ctl live ports).toLayout.before (readings e.output) arena.cube.cells)) →
       SparseCell arena f orig data i.val)
    (ownerOrder : ∀ i, (rows i).number.val=globalCell (arena.controlRows u.val frame offsets ctl live ports).toLayout (readings e.output) i.val)
    (pub : Arg → Word w) (built : Memory w)
    (dir : Packing.Directory.Layout)
    (places : ℕ → Placed (Fin dir.entries)) (geom : ℕ → ℕ) (extra : ℕ → List Record)
set_option quotPrecheck false
local notation "a" => arena.cube
local notation "rows₀" => arena.controlRows u.val frame offsets ctl live ports
local notation "mem" => readings e.output
local notation "bank" => readings orig
local notation "cells" => e.globalCells (team:=u.val) (frame:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live) (ports:=ports) rows

variable {p d R H B : ℕ}
    (D : LengthDeclaration arena.cube.n arena.cube.header.d)
    (label : Fin arena.cube.cells → Label (arena.cube.n+1) arena.cube.header.d)
    (recv : A → Fin arena.cube.cells) (incoming : A → ℕ) (assigned : ℕ → ℕ)
local notation "owner" => scheduledCellOwner arena.cube D label assigned

variable {J : ℕ} (L : ReportLayout) (home : Fin J → Fin arena.cube.cells) (payload : Fin J → ReportBundle)
    (eb supply privateWidth : ℕ → ℕ) (digits : ℕ → Fin L.gadgets → Fin L.countWidth → Bool)
    (tape : ℕ → Bool) (position : ℕ → ℕ)
local notation "baseRow" => sourceCell L home payload eb supply privateWidth digits
local notation "sample" => fun c : Fin arena.cube.cells => (baseRow c.val).withTape tape (position c.val)

include ownerOrder in
omit [Fintype A] in
set_option maxHeartbeats 1800000 in
/-- On this particular native report proposal, the physical private-entry table
pays for the placed opaque boxes and the source report rows. The same increasing
global owner scan supplies the scanner input, for all sampled count and use
bits and the corresponding per-cell tape positions. -/
theorem SparseReportSources.localLaunch
    (src : SparseCallInput pub built) (roster : ProducedRoster arena rows₀ mem places geom extra src)
    (fp : (pub 0).val=frame) (image : readings built=(rows₀).toLayout.published mem)
    (ownedRows : src.owned=fun j => cells (globalCell (rows₀).toLayout mem j))
    (typed : src.tasks=fun j => (SparseExterior.supplementalRow rows₀ mem src.layout cells places geom extra j).typed)
    {z ns ne np nc : ℕ} {bits : P → ℕ} (N : Network z P bits) (host : N.Site → Fin arena.cube.cells)
    (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin np) (ord : N.CrossingEdge host ≃ Fin nc)
    (cables : CableRows N host edge port f.host bank)
    (pp lp : ℕ → ℕ × ℕ)
    (physicalRows : (List.range f.count).map (f.row bank)=dir.directory pp lp)
    (located : RowLocations (dir.directory pp lp) (Fin.val : Fin arena.cube.cells → ℕ) recv incoming)
    (boxRows : dir.OriginalBoxRows pp (fun c : Fin arena.cube.cells => places c.val))
    (bundleEntry : Fin J ↪ Fin dir.entries) (sentTo : ∀ j, (pp (bundleEntry j).val).1=(home j).val)
    (literal : 0<dir.literal/2) (descriptionFits : dir.description≤dir.literal/2)
    (pairBound : ∀ pair, load (cablePair ord (crossSrc N host) (crossDst N host) label)
      (crossWidth N host ∘ ord.symm) pair ≤ arena.cube.header.blocks*(arena.cube.h*arena.cube.b))
    (template : LiveWords.Template E I (Fin dir.entries) ns (arena.cube.cells+1))
    (site : Fin ns → Fin (arena.cube.cells+1)) (arg : E → ℕ) (emit : Fin ns → I → ℕ)
    (shape : TypedBatch.SourceFootprint (fun c => places c.val) (template.directory site arg emit))
    (pubRoom : (arena.cube.cells+1)+template.atoms.length+(arena.cube.cells+1) ≤ 2^p)
    (descRoom : (arena.cube.cells+1)+(Schema.coords template.chunkLabels.length).length+(arena.cube.cells+1) ≤ 2^d)
    (cursor : Fin arena.cube.cells → LocalReportCursor)
    (base : Fin arena.cube.cells → ℕ) (source : Fin arena.cube.cells → ℕ → ℕ)
    (rowTail : ∀ j, (rows j).tail.length=(baseRow (rows j).number.val).tailWidth)
    (counts : ∀ c : Fin arena.cube.cells, (places c.val).reports.length=L.gadgets)
    (fieldDigits : ∀ c : Fin arena.cube.cells, ∀ g ∈ (places c.val).reports, g.length=L.countWidth)
    (body : ∀ c < (rows₀).cells, (rows₀).owner mem c=(rows₀).team → ∀ j,
      (places c).headerWidth+(boxBody ((places c).factors j)).length ≤ dir.description)
    (owners : ∀ c : Fin arena.cube.cells, (rows₀).owner mem c.val=owner c)
    (bind : ∀ c, owner c=u.val → extra c.val=bindingRows (((sample) c).bundles) (cursor c))
    (bundles : ∀ c, owner c=u.val → bundleInputs w L dir.description (((sample) c).bundles) (cursor c) (base c) (source c))
    (marked : ((c : {c : Fin arena.cube.cells // owner c=u.val}) × UsePositions (((sample) c.val).bundles)) ↪
      Diagonal.CellEntries.PowerSlot (Fin R) (Fin H) B)
    {buf : Memory w} {q : ReportCursor}
    (seed : PreparedReportInput pub buf
      (sourceCells L home payload u.val ((rows₀).owner mem) eb supply privateWidth digits) q dir.description) :
    ∃ S : SparseReportSources (Fin dir.entries) E I P a D label recv incoming assigned u.val dir.description p d R H B src f bank rows₀ mem,
      S.LocalReadback (team:=u) geom places extra cells (sample)
        (sourceCells L home payload u.val ((rows₀).owner mem) eb supply privateWidth digits)
        (((List.range arena.cube.cells).filter (fun c => decide ((rows₀).owner mem c=u.val))).map
          (fun c => (baseRow c).withTape tape (position c))) ∧
      PreparedReportInput pub buf (S.reportRows (team:=u)) q dir.description := by
  let hidden := dir.privateBitDelivery pp lp _ boxRows.entry Fin.valEmbedding recv incoming located boxRows.received literal descriptionFits
  have groupCount (c : Fin arena.cube.cells) : (((sample) c).bundles).length=(sourceRows home c.val).length := by
    simp only [ReportCell.withTape,tapeBundles_length,sourceCell,List.length_map]
  let reports := dir.reportBitDelivery pp lp home _ groupCount bundleEntry sentTo recv incoming located literal descriptionFits
  have tails (j) : (rows j).tail.length=(((sample) (rows j).number).tailWidth) :=
    (rowTail j).trans (ReportCell.withTape_tailWidth ..).symm
  let S := SparseReportSources.ofEmitted e rows ownerOrder pub built places geom extra D label recv incoming assigned
    src roster fp image ownedRows typed N host edge port ord cables (physicalRows ▸ located) pairBound template site arg emit
    shape pubRoom descRoom L (sample) cursor base source tails counts fieldDigits hidden reports body owners bind bundles marked
  let atCell := fun c => (baseRow c).withTape tape (position c)
  have scanned := S.reportRows_scan (team:=u) atCell ((rows₀).owner mem) owners (fun _ _ => rfl)
  have shape : eraseReportBits (sourceCells L home payload u.val ((rows₀).owner mem) eb supply privateWidth digits) =
      eraseReportBits (S.reportRows (team:=u)) := by
    rw [scanned]
    exact (eraseReportBits_localTapes _ baseRow (fun _ => tape) position).symm
  refine ⟨S,⟨rfl,rfl,rfl,rfl,rfl,heq_of_eq rfl,heq_of_eq scanned,heq_of_eq shape⟩,?_⟩
  exact S.preparedAtLocalTapes (team:=u) baseRow ((rows₀).owner mem) owners seed (fun _ => tape) position (fun _ _ => rfl)

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
