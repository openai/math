import OAI.Computability.BorderVNP.PackedBottomWeightedTagRead
import OAI.Computability.BorderVNP.PackedBottomWiredSite
import OAI.Computability.BorderVNP.DiagonalBottomBundleAlive
import OAI.Computability.BorderVNP.DiagonalBottomScalarCounts

/-! # Pointwise read of the actual tagged seed program at its original inputs

Every original copy may prescribe its own hidden fine assignment. Its grouped
tile then has a unique compatible successful work bank exactly when the tagged
tile term survives. Its observations record no replacement-gadget occurrences.
-/

namespace OAI
namespace Computability
namespace BorderVNP

set_option maxHeartbeats 2200000

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse CellAddresses BottomGridBank BottomReports Inherited GridBoxes
open GridPlacement Cover TeamContraction ParseBatch ParseBatchVerifier Prewire
open VPVNP VPVNP.ParseGrammar Diagonal.CellEntries Diagonal.ExternalSew
open scoped Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)

local notation "Tile₀" => (Fin q → Deck (depth+2))
local notation "cardV" => GridHosts.tileCount q depth
local notation "net₀" => W.routedFine position
local notation "owner₀" => GridPlacement.cell position W.route
local notation "packing₀" => routedPacking position W.route (fun _ => le_rfl)
local notation "liveLane" => GridHosts.wiredLane G cardV Fintype.card_pos
local notation "width₀" => (fun _ : Fin cardV => GridHosts.inputBlockWidth r n q depth)
local notation "cap₀" => seedSiteCapacity n r q depth
local notation "h₀" => seedChannelWidth n r q depth
local notation "rule₀" => W.routedRules position (sidecarReport code)
local notation "pack₀" => W.seedGrouped position
local notation "at₀" => W.seedLane_aligned position

/-- Equality used in the true conditioned prewire tables at each public tile. -/
noncomputable local instance tagReadDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _

variable {ns ne np qe qa : ℕ} (siteID : (W.routedFine position).Site ↪ Fin ns) (edgeID : (W.routedFine position).Edge ↪ Fin ne)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin np) (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (c : Fin q → Deck (depth+2))

variable {copies : ℕ} {Gadget : Type} (number : Gadget ↪ ℕ)

local notation3 "sl" => W.seedSlab position code siteID edgeID portID c
local notation3 "birth" => W.seedBorn position code siteID edgeID portID channels groups c copies

/-- The original guessed digits at this host lie at the start of each
one-copy work slab, whose physical extent is paid separately for every copy. -/
theorem seedBorn_work : (birth).work = copies*(sl).stride := rfl

/-- Fix precisely the independent internal fine wires of each original copy;
supplied lanes, staged use bits and the zero tail are checked by the actual program. -/
noncomputable def seedBirthPredicate (z : Fin copies → W.Hidden position) (work : ℕ → Bool) : Prop :=
  ∀ (i : Fin copies) (k : Fin (sl).guessed), work (i.val*(sl).stride+k.val) =
    ((guessedWords net₀ owner₀ c edgeID).symm (z i c)) k

/-- The complete tagged fiber of the routed grouped seed at arbitrary original
cable and port words and every tuple of original hidden assignments. -/
noncomputable def seedTagRead (z : Fin copies → W.Hidden position)
    (a : Incident (BottomRepeat.wide pack₀ copies) c → Fin (copies*h₀) → Bool)
    (x : ∀ p : Attached (BottomRepeat.wide pack₀ copies) c, Fin (copies*width₀ p.val) → Bool) :
    Site.TagRead birth (inputWords (BottomRepeat.wide pack₀ copies) channels groups c a x)
      (fun work => W.seedBirthPredicate position code siteID edgeID portID c z (Site.Programs.extendWork work))
      ((W.bundle (Gadget := Gadget) position copies z).tags c a x) number := by
  apply weightedTagRead net₀ owner₀ position packing₀ width₀ order liveLane at₀ siteID edgeID portID channels groups
    c (fun v => rule₀ v.val) copies (3*cap₀) cap₀ (W.seed_stride_le position c) (W.seed_sites_le position c)
  · rw [W.bundle_alive_compact position c z a x]
    have hc (i : Fin copies) := W.seed_alive_compact (Gadget := Gadget) position (sidecarReport code) edgeID portID
      channels groups c copies (z i) i a x
    exact ⟨fun h => ⟨fun i => ((hc i).mp (h i)).1,fun i => ((hc i).mp (h i)).2⟩,
      fun h i => (hc i).mpr ⟨h.1 i,h.2 i⟩⟩
  · exact W.bundle_no_gadgets position z c a x

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
