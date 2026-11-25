import OAI.Computability.BorderVNP.PackedGridSeedValue
import OAI.Computability.BorderVNP.DiagonalBottomSubstitution

/-! # Survival of the original physically grouped tile on its independent copies -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.Tracked

open Crossing Packing.Inherited

/-- Transport of a local table when just the external attachment map is rewritten. -/
theorem cast_attach_read {D exp : ℕ} {Team Param Gadget P : Type} [Fintype Team] [Fintype Param]
    {bits : P → ℕ} (N : Network D P bits) (f : P → N.Site) (eq : N.attach=f)
    (t : Tracked Team Param Gadget exp N) (v : N.Site)
    (a : ∀ e : Incident N v, Fin (N.width e.val) → Bool)
    (x : ∀ p : {p : P // f p=v}, Fin (bits p.val) → Bool) :
    (t.castLayout (M:={N with attach:=f}) (by subst f; rfl)).tags v a x =
      t.tags v a (fun p => x ⟨p.val,(congrFun eq p.val).symm.trans p.property⟩) := by
  subst f
  rfl

end Diagonal.CellEntries.Tracked

namespace Packing.DeckGrid.WiredWitness

open Crossing Inherited GridBoxes GridPlacement BottomGridBank CellAddresses Cover TeamContraction
open Diagonal.CellEntries Diagonal.ExternalSew ParseBatch.Prewire
open scoped BigOperators Classical

set_option maxHeartbeats 1800000
variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {Gadget : Type} (c : Fin q → Deck (depth+2)) {copies : ℕ}

/-- Use the finite-site equality of the actual routed seed table. -/
noncomputable local instance seedDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
local notation "width₀" => fun _ : Fin (GridHosts.tileCount q depth) => GridHosts.inputBlockWidth r n q depth
local notation "lane₀" => GridHosts.wiredLane G (GridHosts.tileCount q depth) Fintype.card_pos
local notation "G₀" => W.seedGrouped position
local notation "N₀" => W.routedFine position
local notation "cell₀" => cell position W.route
local notation "H₀" => seedChannelWidth n r q depth

/-- A genuine bundled table is nonzero exactly when every copy passes on
its original private fine wires and the addressed slices of the actual supplied word. -/
theorem bundle_alive_compact (z : Fin copies → W.Hidden position)
    (a : Incident (BottomRepeat.wide G₀ copies) c → Fin (copies*H₀) → Bool)
    (x : ∀ p : Attached (BottomRepeat.wide G₀ copies) c, Fin (copies*width₀ p.val) → Bool) :
    (W.bundle (Gadget := Gadget) position copies z).tags c a x ≠ 0 ↔
      ∀ i : Fin copies, W.seedTags (Gadget := Gadget) position (z i) c (fun e k => a e (finProdFinEquiv (i,k)))
        (argumentWords N₀ cell₀ width₀ order lane₀ (W.seedLane_aligned position) c (fun p k => x p (finProdFinEquiv (i,k)))) ≠ 0 := by
  let attached := (wiredGrid G q depth order position).attach
  have attach_eq : (W.seedGrid position).attach=attached :=
    funext fun p => (W.seedLane_aligned position p).symm
  let part := fun i : Fin copies => (W.seed (Gadget := Gadget) position (z i)).tags c
    (fun e k => a e (finProdFinEquiv (i,k)))
    (fun p _ => x ⟨(lane₀ p.val).1,(GridHosts.wired_aligned G q depth order position p.val).trans p.property⟩
      (finProdFinEquiv (i,(lane₀ p.val).2)))
  change (∏ i, part i) ≠ 0 ↔ _
  simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const]
  apply forall_congr' fun i => ?_
  apply Iff.of_eq
  apply congrArg (· ≠ 0)
  exact Tracked.cast_attach_read (W.seedGrid position) attached attach_eq
    ⟨W.seedTags (Gadget := Gadget) position (z i),W.seedWords position (z i)⟩ c _ _

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
