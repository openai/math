import OAI.Computability.BorderVNP.PackedBankFiniteSeedState
import OAI.Computability.BorderVNP.PackedFieldBoundGrid
import OAI.Computability.BorderVNP.PackedSeedCoreChoices

/-! # The actual signed verifier birth programs on the named bottom state -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Cover Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Packing Packing.DeckGrid Packing.PhysicalEpochs
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction GridPlacement Shortening.PreparedBins
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar Inherited BottomGridBank BottomReports DeckGrid.WiredWitness
open private siteCap_instance from OAI.Computability.BorderVNP.PackedBankFiniteSeedState
open scoped Classical
attribute [local instance] portFintype
set_option maxHeartbeats 2400000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {R r t pins link inner n g d : ℕ} {Edge : Type} [Fintype Edge] {G : Wiring R r t pins link inner n Edge}
    {len : Fin n} {key : Fin g}
    {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order key)
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (siteID : (W.routedFine position).Site ↪ Fin ns) (edgeID : (W.routedFine position).Edge ↪ Fin ne)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin np) (copies : ℕ)

/-- Use the routed grid's equality instance in the signed seed incidence directory. -/
noncomputable local instance wiredSeedDeckEq {q l : ℕ} : DecidableEq (Fin q → Deck (l+2)) := Classical.decEq _

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount (Fintype.card (Cube D)) d
local notation "bw" => fun _ : Fin tiles => GridHosts.inputBlockWidth r n axes d
local notation "lane" => GridHosts.wiredLane G tiles Fintype.card_pos
local notation "pk" => routedPacking position W.route (fun _ => le_rfl)
local notation "degree" => Fintype.card (Direction axes)
local notation "H₀" => seedChannelWidth n r axes d
local notation "K₀" => seedBoxCapacity n r axes d degree
local notation "S₀" => seedSiteCapacity n r axes d
local notation "channels" => Shortening.PublicCapacity.Rows.edge (groupedGridRows G axes d order position copies)
local notation "groups" => Equiv.toEmbedding (Equiv.refl (Fin tiles))
local notation "L₀" => seedBundle G axes d order position copies
local notation3 (prettyPrint := false) "born" v => W.seedBorn position tag siteID edgeID portID channels groups v copies

/-- The signed fine program stores its staged verifier rules and native grammar
report suffix at the very beginning of each routed lineage. -/
noncomputable def wiredSeedPrograms : Site.Programs L₀ := fun v => Site.Lineage.start (born v) rfl

local notation "pr" => wiredSeedPrograms W position tag siteID edgeID portID copies

variable {w : ℕ} (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K) (words : Pins S (d+1) (SelectedSchedule.boundary S (d+1)) w 0 → Bool)
local notation "state₀" => seedState S G d order position copies table words

/-- Present the signed verifier's native lineages in the saved seed state's
layer-zero port enumeration. -/
noncomputable abbrev wiredSeedStatePrograms :
    Site.Programs (seedState S G d order position copies table words).pack.layout :=
  changePrivateInstance _ (wiredSeedPrograms W position tag siteID edgeID portID copies)

/-- Public and full compiler tile budgets and the scalar invariant for the
true signed seed, including its grammar sidecar and copied verifier work. -/
theorem wiredSeedStatePrograms_bounds (dB : ℕ) :
    let programs := wiredSeedStatePrograms S W position tag siteID edgeID portID copies table words
    SiteCap (state₀).route programs.bankFields false (seedPublicBase degree) ∧
    SiteCap (state₀).route programs.fullFields true (baseMass degree K₀ H₀ copies dB) ∧
    ∀ v, (programs v).program.ScalarBound (max (max 2 (max copies K₀)) (max 1 (programs v).program.size)) := by
  intro programs
  let route := seedRoutes S G d order position copies table
  let coord := GridShape.coordinate (d := d+1) (factorEnum D).symm
  let fields := W.seedFields position tag siteID edgeID portID channels groups copies dB
  obtain ⟨oldPub,oldFull⟩ := W.seedFields_siteCap position tag siteID edgeID portID channels groups copies dB table route coord
    (seed_origin S G d order position copies table)
  let outer := portFintype (P := Fin tiles) (k := fan S) (b := 0)
  refine ⟨?_,?_,?_⟩
  · apply siteCap_instance (f := Fin.fintype tiles) (g := outer) route pr false false (seedPublicBase degree)
    intro tile
    have fit := publicRecords_le L₀ pr (fields false) (fun _ => le_rfl) (fun v => reduceMove (d+1) (route.origin v) = tile)
    exact (Nat.add_le_add_left fit 1).trans (oldPub tile)
  · apply siteCap_instance (f := Fin.fintype tiles) (g := outer) route pr true true (baseMass degree K₀ H₀ copies dB)
    intro tile
    have fit := fullRecords_le L₀ pr (fields true) true (fun _ => ⟨le_rfl,Nat.le_add_right ..⟩)
      (fun v => reduceMove (d+1) (route.origin v) = tile)
    exact (Nat.add_le_add_left fit 1).trans (oldFull tile)
  · intro v
    let fine := W.routedFine position
    let N := W.seedGrouped position
    let rules := fun u : {u : fine.Site // cell position W.route u = v} => W.routedRules position (sidecarReport tag) u.val
    let stride := bottomStride (3*S₀+incoming N v) S₀
    have h : (born v).ScalarBound (max 2 (max copies (max stride (born v).size))) := born_scalarBound fine (cell position W.route) position pk bw order lane (W.seedLane_aligned position)
      siteID edgeID portID channels groups v rules copies (3*S₀) S₀
    have room := W.seedBorn_room position v
    have bound : stride ≤ K₀ := (Nat.le_add_left _ _).trans room
    intro a ha
    change a ∈ (born v).markedWords at ha
    have z := h a ha
    change a.2 ≤ max (max 2 (max copies K₀)) (max 1 (born v).size)
    omega

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
