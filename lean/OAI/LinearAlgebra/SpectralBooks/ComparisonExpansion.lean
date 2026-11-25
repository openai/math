import OAI.LinearAlgebra.SpectralBooks.Crossing

/-!
# From strict tensor comparison to an ordinary sum

The comparison theorem gives a restriction of `K` direct copies of
`(⊕ j, Y j)^⊗n`. In coordinates each input to those local maps carries a
copy label and a word of direct-sum tags. Keeping a fixed copy and word
gives a local image of the corresponding product of `Y`'s. Summing the
nonzero images gives the ordinary sum needed by the doubling argument.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace ComparisonExpansion

open scoped BigOperators Classical
open Crossing

noncomputable section

variable {F I : Type*} [CommSemiring F] [Fintype I]

/-- The coefficient function obtained by summing weighted coordinate basis tensors. -/
private def basisSum {A : I → Type*} {S : Type*} [Fintype S]
    (coord : S → ∀ i, A i) (weight : S → F) (x : ∀ i, A i) : F :=
  ∑ s, if x = coord s then weight s else 0

/-- A finite direct sum tags every local coordinate with the same summand index. -/
def directSum {J : Type*} [Fintype J] {A : J → I → Type*} [∀ j i, Fintype (A j i)]
    (Y : (j : J) → (∀ i, A j i) → F) : (∀ i, Σ j, A j i) → F :=
  basisSum (fun p : Σ j, ∀ i, A j i => fun i => ⟨p.1, p.2 i⟩) (fun p => Y p.1 p.2)

/-- Group corresponding coordinates at every site in the tensor product indexed by `w`. -/
def wordProduct {J P : Type*} [Fintype P] {A : J → I → Type*}
    (Y : (j : J) → (∀ i, A j i) → F) (w : P → J)
    (x : (i : I) → (t : P) → A (w t) i) : F :=
  ∏ t, Y (w t) (fun i => x i t)

/-- The corresponding grouped tensor power of a single tensor. -/
def power {A : I → Type*} (Y : (∀ i, A i) → F) (n : ℕ)
    (x : (i : I) → Fin n → A i) : F :=
  ∏ t, Y (fun i => x i t)

private theorem power_basisSum {A : I → Type*} {S : Type*} [Fintype S]
    (coord : S → ∀ i, A i) (weight : S → F) (n : ℕ) :
    power (basisSum coord weight) n =
      basisSum (fun z : Fin n → S => fun i t => coord (z t) i)
        (fun z => ∏ t, weight (z t)) := by
  funext x
  simp only [power, basisSum, Fintype.prod_sum, Fintype.prod_ite_zero]
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  exact propext (by simp only [funext_iff]; exact forall_comm)

private theorem image_basisSum {A B : I → Type*} [∀ i, Fintype (A i)] {S : Type*}
    [Fintype S] (coord : S → ∀ i, A i) (weight : S → F)
    (M : ∀ i, B i → A i → F) (x : ∀ i, B i) :
    (∑ a, basisSum coord weight a * ∏ i, M i (x i) (a i)) =
      ∑ s, weight s * ∏ i, M i (x i) (coord s i) := by
  simp only [basisSum, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

private def splitTags {J P : Type*} (A : J → Type*) :
    (P → Σ j, A j) ≃ Σ w : P → J, (t : P) → A (w t) where
  toFun x := ⟨fun t => (x t).1, fun t => (x t).2⟩
  invFun p t := ⟨p.1 t, p.2 t⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Expanding the comparison restriction supplies one local image for every
pair consisting of a copy and a word. Tensor formats may vary among the `Y j`. -/
theorem restriction_directSum_power {J : Type*} [Fintype J] {A : J → I → Type*}
    [∀ j i, Fintype (A j i)] {B : I → Type*} (Y : (j : J) → (∀ i, A j i) → F)
    (X : (∀ i, B i) → F) (K n : ℕ)
    (h : IsRestriction X (directSum (fun _ : Fin K => power (directSum Y) n))) :
    ∃ Z : Fin K × (Fin n → J) → (∀ i, B i) → F,
      X = ∑ p, Z p ∧ ∀ p, IsRestriction (Z p) (wordProduct Y p.2) := by
  obtain ⟨M, hM⟩ := h
  let M' (p : Fin K × (Fin n → J)) (i : I) (x : B i) (a : (t : Fin n) → A (p.2 t) i) :=
    M i x ⟨p.1, fun t => ⟨p.2 t, a t⟩⟩
  let Z (p : Fin K × (Fin n → J)) (x : ∀ i, B i) :=
    ∑ a, wordProduct Y p.2 a * ∏ i, M' p i (x i) (a i)
  refine ⟨Z, ?_, fun p => ⟨M' p, fun _ => rfl⟩⟩
  funext x
  rw [Finset.sum_apply, hM]
  unfold directSum
  rw [image_basisSum, Fintype.sum_sigma, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp_rw [power_basisSum]
  change (∑ a : (i : I) → Fin n → Σ j, A j i, _ * ∏ i, (fun i u v => M i u ⟨k, v⟩) i (x i) (a i)) = _
  rw [image_basisSum (A := fun i => Fin n → Σ j, A j i) _ _ (fun i u v => M i u ⟨k, v⟩) x]
  let e := splitTags (P := Fin n) (fun j => ∀ i, A j i)
  trans ∑ p : (w : Fin n → J) × ((t : Fin n) → ∀ i, A (w t) i),
    (∏ t, Y (p.1 t) (p.2 t)) * ∏ i, M' (k, p.1) i (x i) (fun t => p.2 t i)
  · exact Fintype.sum_equiv e _ _ fun _ => rfl
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact Fintype.sum_equiv (Equiv.piComm (fun t i => A (w t) i)) _ _ fun _ => rfl

/-- Reindex the nonzero terms of a nonzero finite sum. The map back to the
original index set retains the source of each surviving term. -/
theorem nonzero_terms_of_sum {P M : Type*} [Fintype P] [AddCommMonoid M]
    {x : M} (hx : x ≠ 0) (z : P → M) (hsum : x = ∑ p, z p) :
    ∃ L : ℕ, 0 < L ∧ L ≤ Fintype.card P ∧ ∃ idx : Fin L → P,
      (∀ l, z (idx l) ≠ 0) ∧ x = ∑ l, z (idx l) := by
  let S := {p : P // z p ≠ 0}
  let e := Fintype.equivFin S
  have hex : ∃ p, z p ≠ 0 := by
    by_contra! hz
    exact hx (hsum.trans (by simp [hz]))
  obtain ⟨p, hp⟩ := hex
  refine ⟨Fintype.card S, Fintype.card_pos_iff.mpr ⟨⟨p, hp⟩⟩, Fintype.card_subtype_le _,
    fun l => (e.symm l).1, fun l => (e.symm l).2, ?_⟩
  calc
    x = ∑ p, z p := hsum
    _ = ∑ p ∈ Finset.univ.filter (fun p => z p ≠ 0), z p := (Finset.sum_filter_ne_zero _).symm
    _ = ∑ p : S, z p.1 := Finset.sum_subtype _ (by simp) _
    _ = _ := Fintype.sum_equiv e _ _ fun p => by simp

/-- Discarding zero images gives between one and `K * J^n` actual nonzero
summands, still with a separate restriction witness for each surviving word. -/
theorem nonzero_ordinary_sum_of_comparison {J K n : ℕ} {A : Fin J → I → Type*}
    [∀ j i, Fintype (A j i)] {B : I → Type*} (Y : (j : Fin J) → (∀ i, A j i) → F)
    (X : (∀ i, B i) → F) (hX : X ≠ 0)
    (h : IsRestriction X (directSum (fun _ : Fin K => power (directSum Y) n))) :
    ∃ L : ℕ, 0 < L ∧ L ≤ K * J ^ n ∧ ∃ U : Fin L → (∀ i, B i) → F,
      X = ∑ l, U l ∧ ∀ l, U l ≠ 0 ∧ ∃ w : Fin n → Fin J, IsRestriction (U l) (wordProduct Y w) := by
  obtain ⟨Z, hsum, himage⟩ := restriction_directSum_power Y X K n h
  obtain ⟨L, hL, hcount, idx, hnz, heq⟩ := nonzero_terms_of_sum hX Z hsum
  exact ⟨L, hL, hcount.trans_eq (by simp), Z ∘ idx, heq, fun l => ⟨hnz l, (idx l).2, himage _⟩⟩

end
end ComparisonExpansion

end SpectralBooks
end LinearAlgebra
end OAI
