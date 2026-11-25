import OAI.Computability.BorderVNP.PackedGridPublic

/-! # Expanded private items per initial grid cell

The original box and its bounded-degree ends cost a constant per fine vertex apart
from its supplied private table description. Each additional routing visit contributes
at most five more expanded items. The public topology charges one descriptor per
directed cable end regardless of the private use of that channel.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridPlacement

open Crossing Shortening Finset
open scoped Classical
variable {D : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits)

private theorem testedWidth_const {E : Type*} [Fintype E] (w : ℕ) (test : E → Prop) :
    testedWidth (fun _ : E => w) test = (univ.filter test).card * w := by
  unfold testedWidth
  rw [← sum_filter, sum_const,nsmul_eq_mul]
  rfl

private theorem testedWidth_le {E : Type*} [Fintype E] (w : E → ℕ) (test : E → Prop) (cap : ℕ)
    (hw : ∀ e, w e ≤ cap) :
    testedWidth w test ≤ (univ.filter test).card * cap := by
  rw [← testedWidth_const]
  apply sum_le_sum
  intro e _
  by_cases hh : test e <;> simp [hh,hw]

/-- A single fine site has at most three wire ends and one external bit port. Its
own box and the payload of its table are charged in the expanded count. -/
theorem fine_site_records [Fintype P] (degree : ∀ v, (univ.filter fun e => N.src e = v).card +
    (univ.filter fun e => N.dst e = v).card ≤ 3) (unit : ∀ e, N.width e ≤ 1)
    (external : ∀ p, bits p ≤ 1) (distinct : Function.Injective N.attach)
    (expanded : Bool) (payload : N.Site → ℕ) (v : N.Site) :
    localRecords N expanded (fun _ => 0) payload (· = v) ≤ 9 + payload v := by
  unfold localRecords
  have hcost {w : ℕ} (hw : w ≤ 1) : recordCost expanded w ≤ 2 := by
    cases expanded with
    | false => simp [recordCost]
    | true => simp [recordCost]; omega
  have hs := testedWidth_le (fun e => recordCost expanded (N.width e)) (fun e => N.src e = v) 2
    (fun e => hcost (unit e))
  have hd := testedWidth_le (fun e => recordCost expanded (N.width e)) (fun e => N.dst e = v) 2
    (fun e => hcost (unit e))
  have hp := testedWidth_le (fun p => recordCost expanded (bits p)) (fun p => N.attach p = v) 2
    (fun p => hcost (external p))
  have h1 : (univ.filter fun p => N.attach p = v).card ≤ 1 :=
    card_le_one.mpr fun _ ha _ hb => distinct ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
  have hb : testedWidth (fun i => boxCost expanded 0 (payload i)) (· = v) ≤ 1+payload v := by
    simp [testedWidth,boxCost,recordCost]
    cases expanded <;> simp
  apply (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hb hs) hd) hp).trans
  have hv := degree v
  omega

/-- The leaf block and the evenly distributed internal sites bound the number of
actual original fine vertices in a cell. -/
theorem occupancy_initial {G : Type} [Group G] [Fintype G] {n : ℕ} (input : P ≃ Fin n)
    (distinct : Function.Injective N.attach) (order : Fin (Fintype.card G) ≃ G) (g : G) :
    (univ.filter fun v => N.initialPlace input distinct order v = g).card ≤
      blockWidth n (Fintype.card G) + blockWidth (Fintype.card N.OtherSite) (Fintype.card G) := by
  let ix := N.siteOrder input distinct
  let addr := initialAddress (Fintype.card_pos (α := G)) n (Fintype.card N.OtherSite)
  have he : (univ.filter fun v => N.initialPlace input distinct order v = g).card =
      (univ.filter fun v => (addr v).1 = order.symm g).card := by
    simp only [card_eq_sum_ones,sum_filter]
    rw [← ix.sum_comp (fun a => if (addr a).1 = order.symm g then (1:ℕ) else 0)]
    apply sum_congr rfl
    intro v _
    simp [Network.initialPlace,addr,ix,← Equiv.eq_symm_apply]
  exact he.trans_le (initial_occupancy (Fintype.card_pos (α := G)) n (Fintype.card N.OtherSite) _)

/-- With private table payloads of size at most `w`, the original records cost at most
`9+w` per fine site in the two blocks that were allocated to the cell. -/
theorem original_cell_records [Fintype P] {G : Type} [Group G] [Fintype G] {n : ℕ} (input : P ≃ Fin n)
    (distinct : Function.Injective N.attach) (order : Fin (Fintype.card G) ≃ G) (g : G)
    (degree : ∀ v, (univ.filter fun e => N.src e = v).card + (univ.filter fun e => N.dst e = v).card ≤ 3)
    (unit : ∀ e, N.width e ≤ 1) (external : ∀ p, bits p ≤ 1)
    (expanded : Bool) (payload : N.Site → ℕ) {w : ℕ} (hw : ∀ v, payload v ≤ w) :
    localRecords N expanded (fun _ => 0) payload (fun v => N.initialPlace input distinct order v = g) ≤
      (blockWidth n (Fintype.card G) + blockWidth (Fintype.card N.OtherSite) (Fintype.card G))*(9+w) := by
  let S := univ.filter fun v => N.initialPlace input distinct order v = g
  have he : (fun v => N.initialPlace input distinct order v = g) = (fun v => id v ∈ S) := by
    funext v; simp [S]
  rw [he,localRecords_near]
  calc
    _ ≤ ∑ _v ∈ S, (9+w) := by
      apply sum_le_sum
      intro v _
      exact (fine_site_records N degree unit external distinct expanded payload v).trans
        (Nat.add_le_add_left (hw v) _)
    _ ≤ _ := by
      rw [sum_const,nsmul_eq_mul]
      apply Nat.mul_le_mul_right
      convert! occupancy_initial N input distinct order g using 2
      congr 2
      exact Subsingleton.elim _ _

end Packing.GridPlacement

end BorderVNP
end Computability
end OAI
