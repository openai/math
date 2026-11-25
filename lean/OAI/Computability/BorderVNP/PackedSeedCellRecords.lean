import OAI.Computability.BorderVNP.PackedSeedResourceRate
import OAI.Computability.BorderVNP.PackedBottomBoxCharges
import OAI.Computability.BorderVNP.PackedBankPublicNodes
import OAI.Computability.BorderVNP.PackedGroupedEpochs

/-!
# Physical local records on each original wired grid tile

The regular directed neighbor layout has one source and one destination per
direction at every tile. The repeated bottom bundle has one grouped input
port at that tile, with one copy-sliced word shared by all repeated teams.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open Cover Crossing Diagonal.CellEntries TeamContraction GridPlacement
open Shortening Finset Diagonal.ExternalSew Inherited InheritedBank
open scoped Classical

variable {R r t pins link inner n D : ℕ} {Edge : Type}
    (G : Wiring R r t pins link inner n Edge) (q depth : ℕ)
    (order : Fin (GridHosts.tileCount q depth) ≃ (Fin q → Deck (depth+2)))
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- The actual repeated, grouped input network on which the bottom private
box and all subsequent physical bounds are installed. -/
noncomputable abbrev seedBundle (copies : ℕ) :=
  (wiredGrid G q depth order position).groupedRepeat
    (fun _ : Fin (GridHosts.tileCount q depth) => GridHosts.inputBlockWidth r n q depth) order copies

/-- Use the same decision for product-deck equality in the routed grid and its incidence tests. -/
noncomputable local instance seedCellDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
variable (copies : ℕ)
local notation "N" => seedBundle G q depth order position copies
local notation "H" => seedChannelWidth n r q depth
local notation "g" => GridHosts.inputBlockWidth r n q depth
local notation "J" => Direction q

private theorem src_sum (c : Fin q → Deck (depth+2)) (z : ℕ) :
    (∑ e : (Fin q → Deck (depth+2)) × J, if e.1 = c then z else 0) = Fintype.card J*z := by
  rw [Fintype.sum_prod_type_right]; simp

private theorem dst_sum (c : Fin q → Deck (depth+2)) (z : ℕ) :
    (∑ e : (Fin q → Deck (depth+2)) × J, if e.1*step q (depth+2) e.2 = c then z else 0) =
      Fintype.card J*z := by
  have one (j : J) : (∑ x : Fin q → Deck (depth+2), if x*step q (depth+2) j = c then z else 0) = z := by
    calc
      _ = ∑ x : Fin q → Deck (depth+2), if x = c then z else 0 := Equiv.sum_comp (Equiv.mulRight _) _
      _ = z := by simp
  rw [Fintype.sum_prod_type_right]; simp [one]

private theorem attach_sum (c : Fin q → Deck (depth+2)) (z : ℕ) :
    (∑ i : Fin (GridHosts.tileCount q depth), if order i = c then z else 0) = z := by
  calc
    _ = ∑ v : Fin q → Deck (depth+2), if v=c then z else 0 := Equiv.sum_comp order _
    _ = _ := by simp

/-- Exact source, target, port and box charges, including self-loops and all
zero-filled unused public channels. -/
theorem seed_localRecords (ex : Bool) (prior payload : (N).Site → ℕ) (c : Fin q → Deck (depth+2)) :
    localRecords N ex prior payload (fun v => v=c) =
      boxCost ex (prior c) (payload c) + 2*Fintype.card J*recordCost ex (copies*H) + recordCost ex (copies*g) := by
  let W := recordCost ex (copies*H)
  let Z := recordCost ex (copies*g)
  unfold localRecords testedWidth
  change (∑ v : Fin q → Deck (depth+2), if v=c then boxCost ex (prior v) (payload v) else 0) +
    (∑ e : (Fin q → Deck (depth+2)) × J, if e.1=c then W else 0) +
    (∑ e : (Fin q → Deck (depth+2)) × J, if e.1*step q (depth+2) e.2 = c then W else 0) +
    (∑ i : Fin (GridHosts.tileCount q depth), if order i = c then Z else 0) = _
  rw [src_sum,dst_sum,attach_sum]
  simp only [sum_ite_eq',mem_univ,ite_true,W,Z]
  ring

/-- There are at most two distinct channel records per direction and one
external group. This includes all live records of a one-copy birth box. -/
theorem seed_row_count (c : Fin q → Deck (depth+2)) : Fintype.card (BottomRepeat.Row N c) ≤ 2*Fintype.card J+1 := by
  have hi : Fintype.card (Incident N c) ≤ 2*Fintype.card J := by
    let f (e : (N).Edge) := if (N).src e = c ∨ (N).dst e = c then 1 else 0
    have he : Fintype.card (Incident N c) = ∑ e, f e := by
      rw [← Finset.sum_filter]
      simp [Fintype.card_subtype]
    rw [he]
    have h (e : (N).Edge) : f e ≤ (if (N).src e=c then 1 else 0)+(if (N).dst e=c then 1 else 0) := by
      have split_or (a b : Prop) [Decidable a] [Decidable b] :
          (if a ∨ b then 1 else 0) ≤ (if a then 1 else 0)+(if b then 1 else 0) := by
        by_cases ha : a <;> by_cases hb : b <;> simp [ha,hb]
      exact split_or _ _
    have hs := sum_le_sum (s := univ) (fun e _ => h e)
    rw [sum_add_distrib] at hs
    change _ ≤ (∑ e : (Fin q → Deck (depth+2)) × J, if e.1=c then 1 else 0) +
      (∑ e : (Fin q → Deck (depth+2)) × J, if e.1*step q (depth+2) e.2=c then 1 else 0) at hs
    rw [src_sum q depth c 1,dst_sum q depth c 1] at hs; omega
  have ha : Fintype.card (Attached N c) = 1 := by
    let eqv : Attached N c ≃ Unit := Equiv.ofBijective (fun _ => ()) ⟨by
      intro x y _
      apply Subtype.ext
      exact order.injective (x.property.trans y.property.symm), fun _ => ⟨⟨order.symm c,order.apply_symm_apply _⟩,rfl⟩⟩
    exact (Fintype.card_congr eqv).trans Fintype.card_unique
  rw [show Fintype.card (BottomRepeat.Row N c) = Fintype.card (Incident N c)+Fintype.card (Attached N c) from Fintype.card_sum,ha]
  omega

/-- The true one-copy bank's incoming bits, with a self-loop counted once.
The same bound multiplied by the copy count applies to any repeated grid. -/
theorem seed_incoming (c : Fin q → Deck (depth+2)) :
    incoming N c ≤ copies*(2*Fintype.card J*H+g) := by
  have hr := seed_row_count G q depth order position copies c
  let t := order.symm c
  have ha : Fintype.card (Attached N c) = 1 := by
    let eqv : Attached N c ≃ Unit := Equiv.ofBijective (fun _ => ()) ⟨by
      intro x y _
      apply Subtype.ext
      exact order.injective (x.property.trans y.property.symm), fun _ => ⟨⟨t,order.apply_symm_apply _⟩,rfl⟩⟩
    exact (Fintype.card_congr eqv).trans Fintype.card_unique
  rw [show Fintype.card (BottomRepeat.Row N c) = Fintype.card (Incident N c)+Fintype.card (Attached N c) from Fintype.card_sum,ha] at hr
  have hi : Fintype.card (Incident N c) ≤ 2*Fintype.card J := by omega
  apply (incoming_eq_widths (N) c).le.trans
  change (∑ _ : Incident N c, copies*H) + (∑ _ : Attached N c, copies*g) ≤ _
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,ha,one_mul]
  calc
    _ ≤ 2*Fintype.card J*(copies*H) + copies*g := Nat.add_le_add_right (Nat.mul_le_mul_right _ hi) _
    _ = _ := by ring

end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
