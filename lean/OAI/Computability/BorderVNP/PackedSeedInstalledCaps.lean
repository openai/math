import OAI.Computability.BorderVNP.PackedSeedBaseCaps

/-! # Transport of the real birth fields to an installed grid -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Cover Crossing Diagonal.CellEntries TeamContraction GridPlacement Shortening Shortening.Adaptive
open Diagonal.ExternalSew GridBoxes BottomReports BottomGridBank Inherited Epoch Epoch.Round PhysicalEpochs
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (GridHosts.tileCount q depth) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- Use the same decision for product-deck equality in the routed grid and its incidence tests. -/
noncomputable local instance seedInstallDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
local notation "H₀" => seedChannelWidth n r q depth
local notation "deg" => Fintype.card (Direction q)
local notation "K₀" => seedBoxCapacity n r q depth deg

variable (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {ns ne np qe qa : ℕ} (siteID : (W.routedFine position).Site ↪ Fin ns)
    (edgeID : (W.routedFine position).Edge ↪ Fin ne) (portID : (Fin r × Fin (publicWidth G)) ↪ Fin np)
    (channelID : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groupID : Fin (GridHosts.tileCount q depth) ↪ Fin qa)


variable (copies dB : ℕ)
local notation "N₀" => seedBundle G q depth order position copies

local notation "fields" => W.seedFields position code siteID edgeID portID channelID groupID copies dB

variable {K : Type*} {p : Pack D (Fin (GridHosts.tileCount q depth)) (fun _ => copies*GridHosts.inputBlockWidth r n q depth) K}

/-- The true initialized fields on a pack whose installed physical layout is
the published grouped wired grid. -/
noncomputable def installedSeedFields (installed : p.layout = N₀) (expanded : Bool) : RecordData p.layout :=
  cast (congrArg RecordData installed.symm) (fields expanded)

/-- A stored input may use any equivalent numbering of the chosen deck
coordinates. Transport the real private birth fields to this physical
layout before propagating the geometric caps. -/
theorem installedSeed_cap {I : Type} [Fintype I] {lev : ℕ} {L : ℝ}
    (installed : p.layout = N₀) (route : SiteRoutes p I lev L)
    (coord : (Fin q → Deck (depth+2)) ≃ (I → Deck (lev+1)))
    (origins : ∀ v, reduceMove lev (route.origin v) = coord (cast (congrArg Crossing.Network.Site installed) v)) :
    SiteCap route (W.installedSeedFields position code siteID edgeID portID channelID groupID copies dB installed false)
      false (seedPublicBase deg) ∧
    SiteCap route (W.installedSeedFields position code siteID edgeID portID channelID groupID copies dB installed true)
      true (baseMass deg K₀ H₀ copies dB) := by
  cases p with
  | mk layout table =>
    change layout = N₀ at installed
    subst layout
    have test (c : I → Deck (lev+1)) :
        (fun v => reduceMove lev (route.origin v) = c) = (fun v => v=coord.symm c) := by
      funext v; rw [origins]; exact propext coord.eq_symm_apply.symm
    constructor
    · intro c; rw [test c]
      exact (W.seedFields_cell position code siteID edgeID portID channelID groupID copies dB _).1
    · intro c; rw [test c]
      exact (W.seedFields_cell position code siteID edgeID portID channelID groupID copies dB _).2

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
