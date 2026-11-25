import OAI.Computability.BorderVNP.PackedGridSeedTape
import OAI.Computability.BorderVNP.PackedGridCompactRead

/-! # Seed-term survival on the exact native repeated grouped input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes GridPlacement BottomGridBank CellAddresses Inherited Cover TeamContraction
open Diagonal.CellEntries Diagonal.ExternalSew ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped BigOperators Classical
variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {Gadget : Type} (report : WeightSites n g r d → Port)
    {m p qe qa : ℕ} (edgeID : (W.routedFine position).Edge ↪ Fin m) (portID : (Fin r × Fin (publicWidth G)) ↪ Fin p)
    (channelID : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe) (groupID : Fin (GridHosts.tileCount q depth) ↪ Fin qa)
    (c : Fin q → Deck (depth+2)) (copies : ℕ)

/-- Use the same equality instance as the actual conditioned deck-grid table. -/
noncomputable local instance seedValueDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
local notation "width₀" => fun _ : Fin (GridHosts.tileCount q depth) => GridHosts.inputBlockWidth r n q depth
local notation "lane₀" => GridHosts.wiredLane G (GridHosts.tileCount q depth) Fintype.card_pos
local notation "pack₀" => routedPacking position W.route (fun _ => le_rfl)
local notation "G₀" => W.seedGrouped position
local notation "N₀" => W.routedFine position
local notation "cell₀" => cell position W.route
local notation "H₀" => seedChannelWidth n r q depth
local notation "input₀" => inputWords (BottomRepeat.wide G₀ copies) channelID groupID c

/-- For each copy, the actual native padding/Boolean tests agree with the true
formal seed tag on the wide cable lanes and the grouped processor word supplied
to this physical site. -/
theorem seed_alive_compact (z : W.Hidden position) (i : Fin copies)
    (a : Incident (BottomRepeat.wide G₀ copies) c → Fin (copies*H₀) → Bool)
    (x : ∀ p : Attached (BottomRepeat.wide G₀ copies) c, Fin (copies*width₀ p.val) → Bool) :
    W.seedTags (Gadget := Gadget) position z c (fun e k => a e (finProdFinEquiv (i,k)))
      (argumentWords N₀ cell₀ width₀ order lane₀ (W.seedLane_aligned position) c (fun p k => x p (finProdFinEquiv (i,k)))) ≠ 0 ↔
      publicPad N₀ cell₀ position pack₀ width₀ order channelID groupID c
        (scalarSlice (H := H₀) (src := fun e : (Fin q → Deck (depth+2)) × Direction q => e.1)
          (dst := fun e => e.1*step q (depth+2) e.2) N₀ cell₀ position width₀ order channelID groupID c copies (input₀ a x) i) ∧
      finePass N₀ cell₀ edgeID portID c (fun v => W.routedRules position report v.val) ((guessedWords N₀ cell₀ c edgeID).symm (z c))
        (scalarFine N₀ cell₀ position pack₀ width₀ order lane₀ (W.seedLane_aligned position) edgeID portID channelID groupID c copies (input₀ a x) i) := by
  apply (W.seed_alive (Gadget := Gadget) position report z c _ _).trans
  apply and_congr
  · exact (copy_publicPad N₀ cell₀ position pack₀ width₀ order lane₀ (W.seedLane_aligned position) channelID groupID c copies i a x).symm
  · have hu := copy_supplied_pull N₀ cell₀ position pack₀ width₀ order lane₀ (W.seedLane_aligned position) edgeID portID
      channelID groupID c copies i a x
    have hf := finePass_cellRead N₀ cell₀ position pack₀ z edgeID portID c (W.routedRules position report)
      (fun e k => a e (finProdFinEquiv (i,k))) (argumentWords N₀ cell₀ width₀ order lane₀ (W.seedLane_aligned position) c
        (fun p k => x p (finProdFinEquiv (i,k))))
    exact hf.symm.trans (Iff.of_eq (congrArg (finePass N₀ cell₀ edgeID portID c (fun v => W.routedRules position report v.val)
      ((guessedWords N₀ cell₀ c edgeID).symm (z c))) hu.symm))

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
