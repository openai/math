import OAI.Computability.BorderVNP.DiagonalBottomSeedLaneRead
import OAI.Computability.BorderVNP.DiagonalNativeBirthInputs
import OAI.Computability.BorderVNP.PackedBottomInstalledFine

/-! # Exact fine prefix of a physically passing bottom-site occurrence -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site.Lineage

open Crossing Diagonal.CellEntries Site.Programs
open private bits_right from OAI.Computability.BorderVNP.PackedInheritedStaging

/-- A retained checker presents the original public input immediately after
the original work. Each valid address reads the corresponding actual birth lane. -/
theorem birthBank_input {D ne np : ℕ} {P : Type} [Fintype P] {bitsP : P → ℕ}
    (N : Network D P bitsP) (edges : N.Edge ↪ Fin ne) (ports : P ↪ Fin np) (v : N.Site)
    (p : Lineage (Inherited.incoming N v)) (x : PowerInput N) (work : Fin p.birth.work → Bool) (j : Fin p.birth.incoming) :
    let current := inputWords N edges ports v (fun u => x.edges u.val) (fun u => x.ports u.val) ∘ Fin.cast p.size
    bits work (p.retention.readInput current) (p.birth.work+j.val) = birthInput N edges ports v p x j.val := by
  intro current
  refine (bits_right work (p.retention.readInput current) j).trans ?_
  simp only [birthInput,extendWork,dite_eq_left j.isLt,current]

end Packing.Inherited.Site.Lineage

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse CellAddresses BottomGridBank BottomReports Inherited GridBoxes
open GridPlacement Cover TeamContraction ParseBatch ParseBatchVerifier Prewire
open VPVNP VPVNP.ParseGrammar Diagonal.CellEntries Diagonal.ExternalSew
open scoped Classical
set_option maxHeartbeats 1600000

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)

/-- Equality of deck tiles in the named native fine slab. -/
noncomputable local instance birthBitEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
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
    (birthBank bank : ℕ → Bool) (base : ℕ) (i : Fin copies) (z : W.Hidden position)
local notation "slab" => W.seedSlab position code sites edges ports c
local notation "wide₀" => BottomRepeat.wide grouped₀ copies
local notation "slice₀" => copyInput (H := h₀) (src := fun a : Tile₀ × Direction q => Prod.fst a)
  (dst := fun a => Prod.fst a*step q (depth+2) (Prod.snd a)) net₀ owner₀ position width₀ order channels groups c
local notation "idx₀" => publicIndex net₀ owner₀ position packing₀ width₀ order lane₀ (W.seedLane_aligned position) edges ports channels groups c
local notation "input₀" => inputWords wide₀ channels groups c (fun e => PowerInput.edges a (Subtype.val e)) (fun p => PowerInput.ports a (Subtype.val p))

/-- A real checked copy's original fine bits consist of its free hidden choices
and the physically tied inputs of that same copy. Here the full restored input
may depend on the retained site and on the particular cube path. -/
theorem seedCopyInput_physicalBits
    (suffix : ∀ j : Fin (incoming wide₀ c), birthBank (copies*(slab).stride+j.val) = input₀ j)
    (window : ∀ j : Fin (slab).stride, bank (base+i.val*(slab).stride+j.val) = birthBank (i.val*(slab).stride+j.val))
    (guesses : ∀ j : Fin (slab).guessed, birthBank (i.val*(slab).stride+j.val) = ((guessedWords net₀ owner₀ c edges).symm (z c)) j)
    (reported : Fin (slab).used → Bool)
    (checks : (slab).Checks (fun j => birthBank (i.val*(slab).stride+j))
      (fun j => slice₀ copies (slab).stride birthBank i (idx₀ j)) (slice₀ copies (slab).stride birthBank i) reported)
    (j : Fin (stride net₀ owner₀ c)) :
    bank (base+i.val*(slab).stride+j.val) = physicalBits owner₀ position z packing₀ edges ports c
      (fun u => (W.seedCopyInput position a i).edges u.val) (fun u => (W.seedCopyInput position a i).ports u.val) j := by
  have boundary (k : Fin (slab).supplied) : slice₀ copies (slab).stride birthBank i (idx₀ k) =
      scalarFine net₀ owner₀ position packing₀ width₀ order lane₀ (W.seedLane_aligned position)
        edges ports channels groups c copies input₀ i k := suffix _
  have fine := W.seedCopyInput_fine position a i edges ports channels groups c
  refine (window ⟨j.val,(slab).fine_room j⟩).trans ?_
  obtain ⟨g,rfl⟩ := (finSumFinEquiv (m := guessedSize net₀ owner₀ c) (n := suppliedSize net₀ owner₀ c)).surjective j
  rcases g with k | k
  · simpa only [physicalBits,copyBits,finSumFinEquiv_symm_apply_castAdd,Sum.elim_inl,finSumFinEquiv_apply_left,Fin.val_castAdd] using guesses k
  · simp only [physicalBits,copyBits,finSumFinEquiv_apply_right,finSumFinEquiv_symm_apply_natAdd,Sum.elim_inr,Fin.val_natAdd]
    exact (checks.1 k).trans ((boundary k).trans (congrFun fine k))

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
