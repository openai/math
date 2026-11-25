import OAI.Computability.BorderVNP.PackedHistoryOuterPrivateSites
import OAI.Computability.BorderVNP.DiagonalSewnTrackedPowerRead
import OAI.Computability.BorderVNP.DiagonalFlatBirthInput
import OAI.Computability.BorderVNP.DiagonalEnrichedSewnTagModels

/-! # The old native checker input on one exterior-sewn routed host

The last private stage forces every old incidence lane to its new cable or
free position, or to zero. Its ordered physical birth vector agrees with
the same reconstructed terminal input used to evaluate the original power slot.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Packing Inherited Diagonal.CellEntries BorderVNP.Cube BorderVNP.Cube.Physical
open private extendWires from OAI.Computability.BorderVNP.PackedInheritedRoundValue
open scoped Classical

variable {D n d blocks b h K s : ℕ} {A Cell : Type} [DecidableEq Cell] {bits : A → ℕ}
    (N : Network D A bits) {cell : N.Site → Cell} (slot : LiveBit N cell ↪ Slot n d blocks (h*b))
    (a : Physical.Path N cell n d blocks b h K s) (bank : Ports bits) (v : N.Site)

/-- Keep this site's actual routed cable endpoints and the complete supplied
free bank. All extensions away from the site are immaterial to its checker. -/
noncomputable def atPathHost : PowerInput N :=
  ⟨extendWires N v (pathEdges slot a v),bank⟩

/-- Restricting the path-host input to its incidence cables recovers each original
path half-edge bit, including at loops. -/
theorem atPathHost_edges (e : Incident N v) :
    (atPathHost N slot a bank v).edges e.val = pathEdges slot a v e := by
  funext j
  simp only [atPathHost,extendWires,dite_eq_left e.property]

end Diagonal.ExternalSew

namespace Packing.SewnField

open Crossing Inherited Inherited.Site.Lineage Inherited.Site.Programs
open Diagonal.ExternalSew Diagonal.CellEntries BorderVNP.Cube BorderVNP.Cube.Physical
open scoped Classical
set_option maxHeartbeats 1800000

variable {D ae ap be bp n d blocks b h K s : ℕ} {A P U Free Cable Cell : Type}
    [Fintype A] [Fintype P] [Fintype U] [Fintype Cable] [DecidableEq Cell]
    {bits : A → ℕ} (N : Network D A bits) (lane : P ↪ Σ a, Fin (bits a))
    {cw : Cable → ℕ} (B : Bundle (FineView.layout N lane) Free Cable cw)
    (gw : U → ℕ) (freeLane : Free ↪ Σ u, Fin (gw u)) (owner : U → N.Site)
    (aligned : ∀ f, owner (freeLane f).1 = B.layout.attach f)
    (oldEdge : N.Edge ↪ Fin ae) (oldPort : A ↪ Fin ap)
    (edge : (N.Edge ⊕ Cable) ↪ Fin be) (port : U ↪ Fin bp) (progs : Site.Programs N)
    {cell : N.Site → Cell}

local notation "out" => Network.packExternal (Bundle.layout B) gw owner

/-- The actual zero/copy interval stage restores the original native birth
word, even on a cube path whose two halves of a cut cable disagree. -/
theorem sewnPath_birthInput (slot : LiveBit out cell ↪ Slot n d blocks (h*b))
    (a : Physical.Path out cell n d blocks b h K s) (bank : Ports gw) (v : N.Site) :
    birthInput out edge port v (sewnPrograms N lane B gw freeLane owner aligned oldEdge oldPort edge port progs v)
      (atPathHost out slot a bank v) =
      birthInput N oldEdge oldPort v (progs v) (sewnPathPowerInput N lane B gw freeLane owner slot a bank v) := by
  let w := atPathHost out slot a bank v
  let field : N.Tables (ℕ → Bool) := fun u z x =>
    extendWork ((progs u).retention.readInput (inputWords N oldEdge oldPort u z x ∘ Fin.cast (progs u).size))
  obtain ⟨physical,table⟩ := sewnRead_table N lane B gw freeLane owner aligned oldEdge oldPort edge port field v
    (fun i => w.edges i.val) (fun p => bank p.val)
  have old := B.read (FineView.tables N lane field) w.edges (Network.readExternal gw freeLane bank) v
  exact (congrArg (fun bits => extendWork ((progs v).retention.readInput bits))
    (funext fun j => physical (Fin.cast (progs v).size j))).trans (table.symm.trans old)

end Packing.SewnField

namespace Diagonal.ExternalSew

open Crossing Shortening Cover Adaptive Packing Packing.DeckGrid
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open PublicCapacity CellEntries TeamContraction ParseBatch Inherited
open scoped BigOperators Classical BorderVNP.Epoch.Cube

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

universe u

variable {D m start T : ℕ} [NeZero D] {K E : Type} [Field K] [Field E] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {w : ℕ → ℕ → ℕ}
    {R r t pins link inner n copies : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (axes gridDepth : ℕ) (order : Fin (GridHosts.tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2)))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {deep : S.floor+1+S.drop*T ≤ start} (count : (fan S)^T*copies = R+1)
    {good : ∀ j, EnrichedOuter.State S start (Fin (GridHosts.tileCount axes gridDepth))
      (fun _ => copies*GridHosts.inputBlockWidth r n axes gridDepth) shape W j → Prop}
    (M : EnrichedOuter.Machine.{0,u} deep good V w) (bottom : Admissible good 0)
    (installed : bottom.val.pack.layout = (wiredGrid G axes gridDepth order position).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth)
      order copies)


open BorderVNP.Cube BorderVNP.Cube.Physical Inherited.Site.Lineage Epoch.Round
attribute [local instance] portFintype

variable (rows : ∀ n hn, (M n hn).F.SiteRows) (number : e.Entry → ℕ)
    (seed : Site.Programs bottom.val.pack.layout) {np : ℕ}
    (ports : Port (fan S) (Fin (GridHosts.tileCount axes gridDepth)) T ↪ Fin np)
    (hp : (fieldSewParams G axes gridDepth).Valid) (q : (packHistory bottom M.epoch T).Index)
    {cn cd blocks cb ch ck cs : ℕ} {Cell : Type} [DecidableEq Cell]
    {cell : (enrichedSewnLayout G axes gridDepth order position count M bottom installed q).Site → Cell}
    (slot : LiveBit (enrichedSewnLayout G axes gridDepth order position count M bottom installed q) cell ↪ Slot cn cd blocks (ch*cb))
    (a : Physical.Path (enrichedSewnLayout G axes gridDepth order position count M bottom installed q) cell cn cd blocks cb ch ck cs)
    (bank : Ports (fun _ : FreeBlock R (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth))

/-- The actual sewn private program reads the same original birth input as the
chosen enriched history on its reconstructed terminal words, in the same ordered
edge and port rows used to evaluate the terminal power slot. -/
theorem enrichedSewn_path_birthInput (v : ((packHistory bottom M.epoch T).term q).val.pack.layout.Site) :
    let state := ((packHistory bottom M.epoch T).term q).val
    let sewn := enrichedSewnLayout G axes gridDepth order position count M bottom installed q
    let last := M.terminalPrivatePrograms rows number bottom seed q
    let progs := enrichedSewnPrograms G axes gridDepth order position count M bottom installed (Flat.portRows T ports) hp q last
    birthInput sewn (FieldExport.mergedEdges (fieldSewParams G axes gridDepth) hp state.rows.edge) finProdFinEquiv.toEmbedding
      v (progs v) (atPathHost sewn slot a bank v) =
      birthInput state.pack.layout state.rows.edge ports v (M.historyPrivatePrograms rows number bottom seed T le_rfl q v)
        (enrichedPathPowerInput G axes gridDepth order position count M bottom installed hp.block q slot a bank v) := by
  intro state sewn last progs
  let L := (flattenPack T state.pack).layout
  let h := enrichedBlockHosts G axes gridDepth order position count M bottom installed q
  let fine := GridHosts.groupedLane G (GridHosts.tileCount axes gridDepth) Fintype.card_pos ((fan S)^T) copies count
  let room := GridHosts.gridRoom G (show 0 < GridHosts.tileCount axes gridDepth from Fintype.card_pos)
  have direct := SewnField.sewnPath_birthInput L fine h.bundle (fun _ : FreeBlock R (GridHosts.tileCount axes gridDepth) =>
    GridHosts.inputBlockWidth r n axes gridDepth) (freeLane hp.block room) h.groupOwner (h.groupAligned hp.block room)
    state.rows.edge (Flat.portRows T ports) (FieldExport.mergedEdges (fieldSewParams G axes gridDepth) hp state.rows.edge)
    finProdFinEquiv.toEmbedding last slot a bank v
  exact direct.trans (birthInput_flat T state.pack state.rows.edge ports v
    (M.historyPrivatePrograms rows number bottom seed T le_rfl q v) _)

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
