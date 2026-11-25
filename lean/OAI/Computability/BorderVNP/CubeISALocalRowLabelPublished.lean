import OAI.Computability.BorderVNP.CubeISALocalRowLabelArena
import OAI.Computability.BorderVNP.CubeLabelPublishedVolume

/-! # Label scratch on the compact directory produced by the native geometry

Both incoming sparse tables have their physical widths and valid endpoint
names after the private placement and compact publication. The transmitted
pin vector supplies the chooser's output arrays on that same memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open Crossing Packing Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical
open VPVNP.BurstRAM BorderVNP.Cube CubeHeaderInstall

/-- The actual memory returned by the delivery writer meets all requirements
of the two public label passes, using the physical intercell volume and the
maximum literal demand of all teams for the arithmetic envelope. -/
theorem labelPrefixFits_published {W D s n d k b : ℕ} {pub : Arg → Word W} {f : BroadcastFrame}
    {raw : List Bool} (a : CubeArena.Layout) (old : Fin 81 → Word W)
    (fresh profile gates outputs width off ell : ℕ) (start mid : Memory W)
    (pins : BootPins pub f (jointFields (a.extension old) fresh profile gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) raw start)
    {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Fin a.cells)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin a.cables) (portID : P ↪ Fin n)
    {σ : Type*} [Fintype σ] (F : Fields s a.cables n a.cells d k b σ) {x : σ → Bool}
    (net : Represents N cell aux siteID edgeID portID F x) (code : ∀ c, (F.cells c).val = c.val)
    (small : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k ≤ b) (hb : b ≤ W) (positive : 0 < a.cells)
    (dir : Directory.Layout) (original : Fin dir.entries → N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (block : ∀ key, bits (live key) = dir.block) (bounds : dir.DestinationBounds)
    (fields : 0 < dir.fields) (tails : dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2))
    (origin dest gap : ℕ)
    (img : RoutingOutputs.Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings start))
    (header : RoutingOutputs.Header (pub 0).val origin a.cables a.cells dir.entries (readings start))
    (demand : readings start ((pub 0).val+8) = dest)
    (prior : (pub 0).val+112 ≤ dest) (copy : f.dst+raw.length ≤ dest)
    (clear : (pub 0).val+9 < f.dst ∨ f.dst+raw.length ≤ (pub 0).val+9)
    (cables : origin+a.cables*3 ≤ a.publicBase) (frame : (pub 0).val+58 < a.header.header)
    (alpha : 0 < a.header.d) (top : a.stop < 2^W)
    (envelope : LabelIndex.wordEnvelope a.alphabet (Diagonal.ExternalSew.intercellWidth N cell +
      dir.teams*((dir.fields+1)*(dir.processors*dir.literal))) < 2^W) :
    let base := (pub 0).val
    let q := RoutingOutputs.privateLayout base origin a.cables a.cells dir.entries dir.description gap
    let tables := RoutingOutputs.bases origin a.cables a.cells dir.entries
    let pp := Directory.ISA.placement (readings mid) q.raw
    let lp := Directory.ISA.placement (readings mid) tables.livePairs
    let rows := dir.directory pp lp
    let result := Directory.ISA.publish mid base dest rows
    q.Image (readings start) dir.entries (readings mid) → q.Fits W (readings start) →
    dest+7*rows.length ≤ origin → rows.length < 2^W →
    (∀ i : Fin rows.length, ∀ v ∈ rows[i.val].words, v < 2^W) →
    LabelPrefixFits base W (readings result) := by
  intro base q tables pp lp rows result placed room sep cnt rawFit
  let t := LabelIndex.layout base (readings result)
  obtain ⟨co,cc,loc,rc,cn⟩ := RoutingOutputs.chooser_header (readings start) mid rows header demand
    (show base+11 < origin by omega) (show base+11 < dest by omega) placed cnt
  change t.cables = origin at co
  change t.cableCount = a.cables at cc
  change t.deliveries = dest at loc
  change t.deliveryCount = rows.length at rc
  change t.cells = a.cells at cn
  let l : LabelIndex.Layout := { t with
    cables := origin
    cableCount := a.cables
    deliveries := dest
    deliveryCount := rows.length
    cells := a.cells }
  have same : l = t := by dsimp only [l]; rw [← co,← cc,← loc,← rc,← cn]
  obtain ⟨_,_,ep,_⟩ := RoutingOutputs.after_private_placement l N cell aux siteID edgeID portID F x
    net code small hk hb positive dir original live block bounds base gap (readings start) mid
    img placed room rfl (by change base+9 < origin; omega) (by change base+9 < dest; omega)
    (.inr sep) rawFit
  have volume := CableTriples.published_inputWidth l N cell aux siteID edgeID portID F x net code hk le_rfl hb mid
    (img.cable_after_private F hk hb _ _ base origin dir.description gap (readings start) mid placed)
    dir pp lp base bounds.processors fields bounds.block tails rfl (by change base+9 < dest; omega)
    (by change base+9 < origin; omega) (.inr sep) rawFit
  change LabelIndex.Endpoints l (readings result) at ep
  change LabelIndex.inputWidth l (readings result) ≤ _ at volume
  rw [same] at ep volume
  have finalPins := pins.placedDirectory origin a.cables a.cells dir.entries dir.description gap dest rows
    placed (by omega) (by omega) prior copy clear
  apply finalPins.labelPrefixFits a old fresh profile gates outputs width off ell ep cc cn
    (show t.cables+t.cableCount*3 ≤ a.publicBase by omega)
    (show t.deliveries+t.deliveryCount*7 ≤ a.publicBase by omega) frame alpha top
  change LabelIndex.wordEnvelope a.alphabet (LabelIndex.inputWidth t (readings result)) < 2^W
  apply lt_of_le_of_lt _ envelope
  unfold LabelIndex.wordEnvelope
  gcongr

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
