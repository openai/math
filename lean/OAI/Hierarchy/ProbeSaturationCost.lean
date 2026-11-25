import OAI.Hierarchy.ProbeStagePackedMasks
import OAI.Hierarchy.ProbeStageMaskUpdate
import OAI.Hierarchy.ProbeStageAdviceSize
import Mathlib.Data.Fintype.BigOperators

namespace OAI
/-! # Charging each occurrence list at the unique first saturation -/

namespace Hierarchy.ProbeStage
open Finset
open scoped BigOperators

noncomputable def saturationWrites {B ℓ q : ℕ} (strings : MaskIndex B → Fin ℓ → Fin B)
    (c : Fin B) (rank : Fin q) :=
  if rank.val+1=q then (PackedMask.occurrences strings c).length else 0

/-- At most one record in a fixed block and color can fill the last quota
position. Sum the length of its actual occurrence list. -/
theorem saturation_one_side {R E : Type*} [Fintype R] [Fintype E] {B ℓ q : ℕ}
    (strings : MaskIndex B → Fin ℓ → Fin B) (key : R → E) (color : R → Fin B)
    (rank : R → Fin q) (route : Function.Injective (fun r => (key r,color r,rank r))) :
    ∑ r, saturationWrites strings (color r) (rank r) ≤ Fintype.card E*(B^4*ℓ) := by
  classical
  let S : Finset R := univ.filter fun r => (rank r).val+1=q
  let site (r : R) := (key r,color r)
  let weight (x : E × Fin B) := (PackedMask.occurrences strings x.2).length
  have inj : Set.InjOn site (S : Set R) := by
    intro r hr s hs same
    obtain ⟨hk,hc⟩ := Prod.mk.inj same
    have h₁ : (rank r).val+1=q := (mem_filter.mp hr).2
    have h₂ : (rank s).val+1=q := (mem_filter.mp hs).2
    have hrs : rank r=rank s := Fin.ext (by omega)
    exact route (Prod.ext hk (Prod.ext hc hrs))
  have onlyFull : ∑ r, saturationWrites strings (color r) (rank r) =
      ∑ r ∈ S, weight (site r) := by
    classical
    dsimp only [S]
    rw [Finset.sum_filter]
    rfl
  have each (e : E) : ∑ c : Fin B, weight (e,c) ≤ B^4*ℓ := by
    simpa [weight,PackedMask.occurrences] using MaskUpdate.all_occurrences strings (univ : Finset (Fin B))
  calc
    _ = ∑ x ∈ S.image site, weight x := by rw [onlyFull,Finset.sum_image inj]
    _ ≤ ∑ x : E×Fin B, weight x :=
      Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = ∑ e : E, ∑ c : Fin B, weight (e,c) := Fintype.sum_prod_type _
    _ ≤ ∑ _e : E, B^4*ℓ := Finset.sum_le_sum (fun e _ => each e)
    _ = _ := by simp

/-- The native allocator updates two counters. Both occurrence-list A/B
scatters together cost at most twice the advice mass of the block family. -/
theorem saturation_both_sides {R G : Type*} [Fintype R] [Fintype G] {m B ℓ : ℕ}
    (p : Tiles R G m) (pos : 0<B) (a : Allocation B (leftBlock p pos) (rightBlock p pos))
    (strings : MaskIndex B → Fin ℓ → Fin B) :
    ∑ r, (saturationWrites strings (a.color r) (a.enterRank r)+
      saturationWrites strings (a.color r) (a.exitRank r)) ≤
      2*(Fintype.card G*blocks m B)*(B^4*ℓ) := by
  rw [Finset.sum_add_distrib]
  have u := saturation_one_side strings _ _ _ a.enter_inj
  have v := saturation_one_side strings _ _ _ a.exit_inj
  simp only [Fintype.card_prod,Fintype.card_fin] at u v
  exact (add_le_add u v).trans_eq (by ring)

/-- In the real j-th subdivision round the total number of occurrence
clears is linear in the original number of records. -/
theorem saturation_at_depth {h d j : ℕ} (hd : 1≤d) (hj : j≤rounds d) {G : Type}
    [Fintype G] (card : Fintype.card G=(radix h d)^j)
    (p : Tiles (Fin (2^h)) G (2^widthLog h d j))
    (a : Allocation (radix h d) (leftBlock p (radix_pos h d)) (rightBlock p (radix_pos h d)))
    (strings : MaskIndex (radix h d) → Fin (8*(4*h+2)) → Fin (radix h d)) :
    ∑ r, (saturationWrites strings (a.color r) (a.enterRank r)+
      saturationWrites strings (a.color r) (a.exitRank r)) ≤
      2*(288*d+17)*4^j*2^h := by
  have both := saturation_both_sides p (radix_pos h d) a strings
  rw [card] at both
  have scaled := Nat.mul_le_mul_left 2 (occurrences_at_depth (h:=h) hd hj)
  let B := radix h d
  let k := B^j*blocks (2^widthLog h d j) B
  let t := B^4*(8*(4*h+2))
  change _ ≤ 2*k*t at both
  change 2*(k*(t+B)) ≤ _ at scaled
  have more : 2*k*t ≤ 2*(k*(t+B)) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left k (Nat.le_add_right t B))
  exact both.trans (more.trans (scaled.trans_eq (by ring)))

end Hierarchy.ProbeStage

end OAI
