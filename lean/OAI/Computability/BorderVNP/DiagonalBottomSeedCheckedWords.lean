import OAI.Computability.BorderVNP.DiagonalBottomSeedLaneRead

/-! # True supplied cable and exterior words of the original passing site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse CellAddresses BottomGridBank BottomReports Inherited GridBoxes
open GridPlacement Cover TeamContraction ParseBatch ParseBatchVerifier Prewire
open VPVNP VPVNP.ParseGrammar Diagonal.CellEntries Diagonal.ExternalSew
open private slice_words from OAI.Computability.BorderVNP.FiniteBottomGridModel
open scoped Classical
set_option maxHeartbeats 1600000

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)

/-- Equality of deck tiles in the original supplied-word checker. -/
noncomputable local instance checkedWordDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
local notation "Tile₀" => (Fin q → Deck (depth+2))
local notation "tiles" => GridHosts.tileCount q depth
local notation "lane₀" => GridHosts.wiredLane G tiles Fintype.card_pos
local notation "width₀" => (fun _ : Fin tiles => GridHosts.inputBlockWidth r n q depth)
local notation "net₀" => W.routedFine position
local notation "owner₀" => cell position W.route
local notation "packing₀" => routedPacking position W.route (fun _ => le_rfl)
local notation "grouped₀" => W.seedGrouped position
local notation "wired₀" => wiredGrid G q depth order position
local notation "h₀" => seedChannelWidth n r q depth
variable {ns ne np qe qa : ℕ} (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : (Fin r × Fin (publicWidth G)) ↪ Fin np) (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (c : Fin q → Deck (depth+2)) {copies : ℕ} (a : PowerInput ((wiredGrid G q depth order position).groupedRepeat
      (fun _ : Fin (Fintype.card (Fin q → Deck (depth+2))) => GridHosts.inputBlockWidth r n q depth) order copies))
    (birthBank : ℕ → Bool) (i : Fin copies)
local notation "slab" => W.seedSlab position code sites edges ports c
local notation "wide₀" => BottomRepeat.wide grouped₀ copies
local notation "slice₀" => copyInput (H := h₀) (src := fun a : Tile₀ × Direction q => Prod.fst a)
  (dst := fun a => Prod.fst a*step q (depth+2) (Prod.snd a)) net₀ owner₀ position width₀ order channels groups c
local notation "input₀" => inputWords wide₀ channels groups c (fun e => PowerInput.edges a (Subtype.val e)) (fun p => PowerInput.ports a (Subtype.val p))

local notation "wire₀" => channelRead (H := h₀) (src := fun a : Tile₀ × Direction q => Prod.fst a)
  (dst := fun a => Prod.fst a*step q (depth+2) (Prod.snd a)) net₀ owner₀ position width₀ order channels groups c
local notation "port₀" => argumentRead (H := h₀) (src := fun a : Tile₀ × Direction q => Prod.fst a)
  (dst := fun a => Prod.fst a*step q (depth+2) (Prod.snd a)) net₀ owner₀ position width₀ order lane₀
    (W.seedLane_aligned position) channels groups c

/-- The channel and argument words used by the physical original-box test
are exactly the mathematical seed's cable and exterior bits for this copy. -/
theorem seedCopyInput_checkerWords
    (suffix : ∀ j : Fin (incoming wide₀ c), birthBank (copies*(slab).stride+j.val) = input₀ j) :
    wire₀ (slice₀ copies (slab).stride birthBank i) = (fun e => (W.seedCopyInput position a i).edges e.val) ∧
    port₀ (slice₀ copies (slab).stride birthBank i) = (fun p => (W.seedCopyInput position a i).ports p.val) := by
  let narrow := scalarSlice (H := h₀) (src := fun a : Tile₀ × Direction q => Prod.fst a)
    (dst := fun a => Prod.fst a*step q (depth+2) (Prod.snd a)) net₀ owner₀ position width₀ order channels groups c copies input₀ i
  have eqn : slice₀ copies (slab).stride birthBank i = narrow := funext fun k => suffix _
  have words := slice_words (H := h₀) (src := fun a : Tile₀ × Direction q => Prod.fst a)
    (dst := fun a => Prod.fst a*step q (depth+2) (Prod.snd a)) net₀ owner₀ position width₀ order channels groups c
    copies (fun e => a.edges e.val) (fun p => a.ports p.val) i
  rw [eqn]
  let cables := fun e : Incident grouped₀ c => fun j => a.edges e.val (finProdFinEquiv (i,j))
  let arguments := fun p : Attached grouped₀ c => fun j => a.ports p.val (finProdFinEquiv (i,j))
  constructor
  · funext e j
    exact (congrFun words _).trans ((inputWords_wire grouped₀ channels groups c cables arguments e j).trans
      (W.seedCopyInput_edge position a i e.val j).symm)
  · funext p j
    let u : Attached grouped₀ c := ⟨(lane₀ p.val).1,(W.seedLane_aligned position p.val).trans p.property⟩
    exact (congrFun words _).trans ((inputWords_port grouped₀ channels groups c cables arguments u (lane₀ p.val).2).trans
      (W.seedCopyInput_port position a i p.val j).symm)

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
