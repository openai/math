import OAI.Computability.BorderVNP.PackedCompilerFields
import OAI.Computability.BorderVNP.PackedRoutedBirthCompilerRows
import OAI.Computability.BorderVNP.PackedGridSeedTape

/-! # Compiler fields of the physical prewired batch at the initial history

Every emitted seed uses its selected Boolean verifier, actual Cayley cables
and grouped external lanes. The published one-copy box capacity bounds every
relative field independently of the number of copies or the global ID range.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes GridPlacement BottomGridBank BottomReports Inherited Cover TeamContraction
open Diagonal.CellEntries Diagonal.ExternalSew ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p qe qa : ℕ} (siteID : (W.routedFine position).Site ↪ Fin s) (edgeID : (W.routedFine position).Edge ↪ Fin m)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin p) (channelID : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groupID : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (c : Fin q → Deck (depth+2))
    {K : Type*} [Field K] {b : ℕ} (e : PaidIdentity K D b)

/-- Equality of the finite deck positions used in the prewired batch's physical bank. -/
noncomputable local instance seedFieldsDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
local notation3 "V₀" => GridHosts.tileCount q depth
local notation3 "width₀" => fun _ : Fin V₀ => GridHosts.inputBlockWidth r n q depth
local notation3 "lane₀" => GridHosts.wiredLane G V₀ Fintype.card_pos
local notation3 "pack₀" => routedPacking position W.route (fun _ => le_rfl)
local notation3 "S₀" => seedSiteCapacity n r q depth
local notation3 "K₀" => seedBoxCapacity n r q depth (Fintype.card (Direction q))
local notation3 "rules₀" => fun v => W.routedRules position (sidecarReport code) (Subtype.val v)

set_option maxHeartbeats 2000000 in
/-- The genuine initial program satisfies the complete compiler invariant at any
relative scale containing its eight-row Boolean tables and public one-copy
capacity. Its private input includes the actual report suffix and every zero row. -/
theorem seedBorn_compilerFields (copies V U : ℕ) (h8 : 8 ≤ V) (room : K₀ ≤ V) :
    (W.seedBorn position code siteID edgeID portID channelID groupID c copies).CompilerFields e V U := by
  have tri := W.routedFine_trivalent position
  have extent := W.seedBorn_room position c
  have relative : 3*S₀ + incoming (W.seedGrouped position) c + S₀ ≤ V :=
    ((Nat.le_add_left _ _).trans extent).trans room
  refine ⟨born_compilerRows (W.routedFine position) (cell position W.route) position pack₀ width₀ order lane₀
    (W.seedLane_aligned position) siteID edgeID portID channelID groupID c rules₀ copies (3*S₀) S₀ e tri,?_⟩
  exact born_splitFields (W.routedFine position) (cell position W.route) position pack₀ width₀ order lane₀
    (W.seedLane_aligned position) siteID edgeID portID channelID groupID c rules₀ copies (3*S₀) S₀ V U
    (fun v => ((W.routedFine position).lane_count_le tri.1 v).trans (tri.2 v)) h8
    (W.seed_stride_le position c) (W.seed_sites_le position c) relative

/-- The published seed capacity, enlarged only to accommodate an eight-entry
gate, gives the invariant without a field-size assumption on the caller. -/
theorem seedBorn_compilerFields_canonical (copies U : ℕ) :
    (W.seedBorn position code siteID edgeID portID channelID groupID c copies).CompilerFields e (max 8 K₀) U :=
  W.seedBorn_compilerFields position code siteID edgeID portID channelID groupID c e copies (max 8 K₀) U
    (le_max_left ..) (le_max_right ..)

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
