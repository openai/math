import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm

/-! # Counting rainbow members of uniform set families -/

open Finset

namespace OAI
namespace Combinatorics
namespace Sunflower

private noncomputable def extendColor {α : Type*} {k : ℕ} (hk : 0 < k)
    (U : Finset α) (f : U → Fin k) (x : α) : Fin k := by
  classical
  exact if h : x ∈ U then f ⟨x, h⟩ else ⟨0, hk⟩

/-- Fixing a bijection on a member of the family leaves all colors on its complement free. -/
private theorem card_good_colors {α : Type*} [DecidableEq α] {k : ℕ} (hk : 0 < k)
    (A U : Finset α) (hAU : A ⊆ U) (hA : A.card = k) :
    k.factorial * k ^ U.card ≤
      (univ.filter (fun f : U → Fin k =>
        Function.Bijective (fun x : A => extendColor hk U f x))).card * k ^ k := by
  classical
  let Good := fun f : U → Fin k => Function.Bijective (fun x : A => extendColor hk U f x)
  let join : (A ≃ Fin k) × ((U \ A : Finset α) → Fin k) → (U → Fin k) :=
    fun p u => if h : u.val ∈ A then p.1 ⟨u, h⟩
      else p.2 ⟨u, mem_sdiff.mpr ⟨u.property, h⟩⟩
  have hjoin (p) : Good (join p) := by
    change Function.Bijective (fun x : A => extendColor hk U (join p) x)
    convert p.1.bijective using 1
    funext x
    simp [extendColor, join, x.property, hAU x.property]
  have hinj : Function.Injective join := by
    intro p q h
    apply Prod.ext
    · apply Equiv.ext
      intro x
      have he := congrFun h (⟨x, hAU x.property⟩ : U)
      simpa [join, x.property] using he
    · funext x
      obtain ⟨hxU, hxA⟩ := mem_sdiff.mp x.property
      have he := congrFun h (⟨x, hxU⟩ : U)
      simpa [join, hxA] using he
  have hcount := Fintype.card_le_of_injective
    (fun p => (⟨join p, hjoin p⟩ : {f // Good f})) (fun _ _ h => hinj (congrArg Subtype.val h))
  have e : A ≃ Fin k := Fintype.equivFinOfCardEq (by simpa using hA)
  rw [Fintype.card_prod, Fintype.card_equiv e, Fintype.card_fun] at hcount
  simp only [Fintype.card_coe, hA, Fintype.card_fin] at hcount
  rw [Fintype.card_of_subtype (univ.filter Good) (by simp)] at hcount
  have hsum : (U \ A).card + k = U.card := hA ▸ card_sdiff_add_card_eq_card hAU
  calc
    k.factorial * k ^ U.card =
        (k.factorial * k ^ (U \ A).card) * k ^ k := by rw [← hsum, pow_add, mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ hcount

/-- Some coloring retains at least the fraction `k! / k^k` of a finite uniform family. -/
theorem exists_rainbow_subfamily {α : Type*} {k : ℕ} (hk : 0 < k)
    (F : Finset (Finset α)) (hF : ∀ A ∈ F, A.card = k) :
    ∃ (c : α → Fin k) (G : Finset (Finset α)), G ⊆ F ∧
      (∀ A ∈ G, Function.Bijective (fun x : A => c x)) ∧
      F.card * k.factorial ≤ G.card * k ^ k := by
  classical
  let U : Finset α := F.biUnion id
  let Good := fun (c : U → Fin k) (A : Finset α) =>
    Function.Bijective (fun x : A => extendColor hk U c x)
  let _ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨c, _, hc⟩ := (univ : Finset (U → Fin k)).exists_max_image
    (fun c => (F.filter (Good c)).card) univ_nonempty
  refine ⟨extendColor hk U c, F.filter (Good c), filter_subset _ _, ?_, ?_⟩
  · exact fun _ hA => (mem_filter.mp hA).2
  · have hcount (A) (hA : A ∈ F) := card_good_colors hk A U
        (subset_biUnion_of_mem id hA) (hF A hA)
    have hswap :
        ∑ A ∈ F, (univ.filter (fun c => Good c A)).card =
          ∑ f : U → Fin k, (F.filter (Good f)).card := by
      simp only [card_filter]
      rw [sum_comm]
    have allColors : Fintype.card (U → Fin k) = k ^ U.card := by
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    have htotal :
        F.card * (k.factorial * k ^ U.card) ≤
          (k ^ U.card * (F.filter (Good c)).card) * k ^ k := calc
      _ = ∑ _A ∈ F, k.factorial * k ^ U.card := by simp
      _ ≤ ∑ A ∈ F, (univ.filter (fun c => Good c A)).card * k ^ k :=
        sum_le_sum hcount
      _ = (∑ f : U → Fin k, (F.filter (Good f)).card) * k ^ k := by rw [← sum_mul, hswap]
      _ ≤ (∑ _f : U → Fin k, (F.filter (Good c)).card) * k ^ k :=
        Nat.mul_le_mul_right _ (sum_le_sum hc)
      _ = _ := by simp [allColors]
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < k ^ U.card from Nat.pow_pos hk)
    · simpa only [mul_left_comm, mul_assoc, mul_comm] using htotal

end Sunflower
end Combinatorics
end OAI
