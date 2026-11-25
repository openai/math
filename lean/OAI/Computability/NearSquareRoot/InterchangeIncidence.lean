import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

/-!
# Incidence counts for products of directed rectangles

A rectangle chooses a set of active coordinates, then a local key at each
coordinate. For a fixed endpoint, incidence factorizes coordinate by coordinate.
The innermost nontrivial coordinate can have a different incidence cost.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Rectangles

open scoped Classical

variable {ι J : Type*} [Fintype ι] [Fintype J]

theorem card_incident_sigma_pi (K : J → ι → Type*) [∀ j i, Fintype (K j i)]
    (I : ∀ j i, K j i → Prop) :
    Fintype.card {r : (j : J) × ((i : ι) → K j i) // ∀ i, I r.1 i (r.2 i)} =
      ∑ j, ∏ i, Fintype.card {r : K j i // I j i r} := by
  let e : {r : (j : J) × ((i : ι) → K j i) // ∀ i, I r.1 i (r.2 i)} ≃
      (j : J) × ((i : ι) → {r : K j i // I j i r}) :=
    { toFun := fun ⟨⟨j, r⟩, hr⟩ => ⟨j, fun i => ⟨r i, hr i⟩⟩
      invFun := fun ⟨j, r⟩ => ⟨⟨j, fun i => (r i).val⟩, fun i => (r i).property⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  simpa [Fintype.card_sigma, Fintype.card_pi] using Fintype.card_congr e

private theorem sum_le_choose_mul {p C : ℕ} (g : {s : Finset ι // s.card = p} → ℕ)
    (h : ∀ s, g s ≤ C) :
    ∑ s, g s ≤ (Fintype.card ι).choose p * C := by
  simpa [Fintype.card_finset_len] using
    (Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => h s)

theorem sum_prod_active_le {p B : ℕ} (w : {s : Finset ι // s.card = p} → ι → ℕ)
    (hactive : ∀ s i, i ∈ s.val → w s i ≤ B)
    (hrest : ∀ s i, i ∉ s.val → w s i ≤ 1) :
    ∑ s, ∏ i, w s i ≤ (Fintype.card ι).choose p * B ^ p := by
  apply sum_le_choose_mul
  intro s
  calc
    ∏ i, w s i ≤ ∏ i ∈ s.val, w s i :=
      Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ _) (fun i _ => hrest s i)
    _ ≤ ∏ _i ∈ s.val, B := Finset.prod_le_prod (hactive s)
    _ = B ^ p := by simp [s.property]

theorem sum_prod_special_le {p q l : ℕ} (w : {s : Finset ι // s.card = p} → ι → ℕ)
    (a : (s : {s : Finset ι // s.card = p}) → s.val)
    (hspecial : ∀ s, w s (a s) ≤ q)
    (hactive : ∀ s i, i ∈ s.val → i ≠ (a s : ι) → w s i ≤ l)
    (hrest : ∀ s i, i ∉ s.val → w s i ≤ 1) :
    ∑ s, ∏ i, w s i ≤ (Fintype.card ι).choose p * (q * l ^ (p - 1)) := by
  apply sum_le_choose_mul
  intro s
  have h := (a s).property
  calc
    ∏ i, w s i ≤ ∏ i ∈ s.val, w s i :=
      Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ _) (fun i _ => hrest s i)
    _ = w s (a s) * ∏ i ∈ s.val.erase (a s), w s i := (Finset.mul_prod_erase _ _ h).symm
    _ ≤ q * ∏ _i ∈ s.val.erase (a s), l :=
      Nat.mul_le_mul (hspecial s) (Finset.prod_le_prod fun i hi =>
        hactive s i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1)
    _ = q * l ^ (p - 1) := by simp [Finset.card_erase_of_mem h, s.property]

/-- Count keys given on the active coordinates only. The values off the active
coordinates are stored in the rectangle, and an endpoint determines them uniquely. -/
theorem card_incident_active_complement (p : ℕ) (K A : Type*) [Fintype K] [Fintype A]
    (I : ι → K → Prop) (x : ι → A) {B : ℕ}
    (h : ∀ i, Fintype.card {r : K // I i r} ≤ B) :
    Fintype.card {r : (s : {s : Finset ι // s.card = p}) ×
        ((s.val → K) × ({i : ι // i ∉ s.val} → A)) //
        (∀ i : r.1.val, I i (r.2.1 i)) ∧ ∀ i : {i : ι // i ∉ r.1.val}, r.2.2 i = x i} ≤
      (Fintype.card ι).choose p * B ^ p := by
  let e : {r : (s : {s : Finset ι // s.card = p}) ×
      ((s.val → K) × ({i : ι // i ∉ s.val} → A)) //
      (∀ i : r.1.val, I i (r.2.1 i)) ∧ ∀ i : {i : ι // i ∉ r.1.val}, r.2.2 i = x i} ≃
      (s : {s : Finset ι // s.card = p}) × ((i : s.val) → {r : K // I i r}) :=
    { toFun := fun ⟨⟨s, f, _⟩, hf, _⟩ => ⟨s, fun i => ⟨f i, hf i⟩⟩
      invFun := fun ⟨s, f⟩ => ⟨⟨s, fun i : s.val => (f i).val, fun i : {i : ι // i ∉ s.val} => x i⟩,
        fun i => (f i).property, fun _ => rfl⟩
      left_inv := by
        rintro ⟨⟨s, f, g⟩, hf, hg⟩
        obtain rfl : g = fun i : {i : ι // i ∉ s.val} => x i := funext hg
        rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  apply sum_le_choose_mul
  intro s
  rw [Fintype.card_pi]
  calc
    ∏ i : s.val, Fintype.card {r : K // I i r} ≤ ∏ _i : s.val, B :=
      Finset.prod_le_prod fun i _ => h i
    _ = B ^ p := by simp [s.property]


/-- The anchor stores both endpoint letters. One is fixed by the incident word,
so the anchor contributes at most a single factor of the alphabet size. -/
theorem card_incident_anchor_complement [DecidableEq ι] (p : ℕ) (K A : Type*) [Fintype K]
    [Fintype A] (a : (s : {s : Finset ι // s.card = p}) → s.val)
    (side : Bool) (I : ι → K → Prop) (x : ι → A) {B : ℕ}
    (h : ∀ i, Fintype.card {r : K // I i r} ≤ B) :
    Fintype.card {r : (s : {s : Finset ι // s.card = p}) ×
      ((A × A) × ((s.val.erase (a s) → K) × ({i : ι // i ∉ s.val} → A))) //
      r.2.1.1 ≠ r.2.1.2 ∧ (if side then r.2.1.2 else r.2.1.1) = x (a r.1) ∧
      (∀ i : r.1.val.erase (a r.1), I i (r.2.2.1 i)) ∧
      ∀ i : {i : ι // i ∉ r.1.val}, r.2.2.2 i = x i} ≤
      (Fintype.card ι).choose p * (Fintype.card A * B ^ (p - 1)) := by
  let Raw := (s : {s : Finset ι // s.card = p}) ×
    ((A × A) × ((s.val.erase (a s) → K) × ({i : ι // i ∉ s.val} → A)))
  let Packed := (s : {s : Finset ι // s.card = p}) ×
    (A × ((i : s.val.erase (a s)) → {r : K // I i r}))
  let decode : Packed → Raw := fun ⟨s, b, f⟩ => ⟨s,
    (if side then (b, x (a s)) else (x (a s), b)),
    fun i => (f i).val, fun i : {i : ι // i ∉ s.val} => x i⟩
  trans Fintype.card Packed
  · apply Fintype.card_le_of_injective
      (fun r => (⟨r.val.1, if side then r.val.2.1.1 else r.val.2.1.2,
        fun i => ⟨r.val.2.2.1 i, r.property.2.2.1 i⟩⟩ : Packed))
    intro u v e
    have recover (r : Raw) (hr : ∀ i : {i : ι // i ∉ r.1.val}, r.2.2.2 i = x i)
        (ha : (if side then r.2.1.2 else r.2.1.1) = x (a r.1))
        (hk : ∀ i : r.1.val.erase (a r.1), I i (r.2.2.1 i)) :
        decode ⟨r.1, if side then r.2.1.1 else r.2.1.2,
          fun i => ⟨r.2.2.1 i, hk i⟩⟩ = r := by
      rcases r with ⟨s, ⟨b,c⟩, f, g⟩
      obtain rfl : g = fun i : {i : ι // i ∉ s.val} => x i := funext hr
      cases side <;> simp_all [decode]
    exact Subtype.ext <| (recover u.val u.property.2.2.2 u.property.2.1 u.property.2.2.1).symm.trans
      ((congrArg decode e).trans (recover v.val v.property.2.2.2 v.property.2.1 v.property.2.2.1))
  · dsimp [Packed]
    rw [Fintype.card_sigma]
    apply sum_le_choose_mul
    intro s
    rw [Fintype.card_prod, Fintype.card_pi]
    apply Nat.mul_le_mul_left
    calc
      ∏ i : s.val.erase (a s), Fintype.card {r : K // I i r} ≤
          ∏ _i : s.val.erase (a s), B := Finset.prod_le_prod fun i _ => h i
      _ = B ^ (p - 1) := by simp [Finset.card_erase_of_mem (a s).property, s.property]

end Rectangles

end NearSquareRoot
end Computability
end OAI
