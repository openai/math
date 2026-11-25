import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! # The Hamming Gram matrix for sharing prime-kernel queries

The Gram matrix on q-ary labels detects distances divisible by ℓ. Expanding
the (ℓ−1)-st power by ordered tuples of match indicators gives a feature
space of dimension at most 1 + (1 + L q)^(ℓ−1).
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped BigOperators

abbrev RoutingLabel (L q : ℕ) := Fin L → Fin q

/-- Number of positions at which two labels differ. -/
def routingDistance {L q : ℕ} (v w : RoutingLabel L q) : ℕ :=
  ∑ i, if v i = w i then 0 else 1

/-- The pairing used to test free rectangles in the companion prime kernel. -/
def routingGram (ℓ L q : ℕ) : Matrix (RoutingLabel L q) (RoutingLabel L q) (ZMod ℓ) :=
  fun v w => 1 - (routingDistance v w : ZMod ℓ) ^ (ℓ-1)

theorem routingGram_apply {ℓ L q : ℕ} [Fact ℓ.Prime] (v w : RoutingLabel L q) :
    routingGram ℓ L q v w = if ℓ ∣ routingDistance v w then 1 else 0 := by
  unfold routingGram
  by_cases h : ℓ ∣ routingDistance v w
  · have hz := (ZMod.natCast_eq_zero_iff ..).mpr h
    have hℓ := (Fact.out : ℓ.Prime).one_lt
    simp [h, hz, show ℓ - 1 ≠ 0 by omega]
  · have hz : (routingDistance v w : ZMod ℓ) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    simp [h, ZMod.pow_card_sub_one_eq_one hz]

@[simp] theorem routingGram_self {ℓ L q : ℕ} [Fact ℓ.Prime] (v : RoutingLabel L q) :
    routingGram ℓ L q v v = 1 := by simp [routingGram_apply, routingDistance]

private abbrev Match (L q : ℕ) := Unit ⊕ Fin L × Fin q
private def feature {ℓ L q : ℕ} (v : RoutingLabel L q) : Match L q → ZMod ℓ
  | .inl _ => 1
  | .inr (i, a) => if v i = a then 1 else 0

private def matchWeight (ℓ L q : ℕ) : Match L q → ZMod ℓ
  | .inl _ => L
  | .inr _ => -1

private theorem distance_eq_sum {ℓ L q : ℕ} (v w : RoutingLabel L q) :
    (routingDistance v w : ZMod ℓ) = ∑ i, matchWeight ℓ L q i * feature v i * feature w i := by
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, Fintype.sum_prod_type, matchWeight, feature,
    mul_one]
  have terms (i : Fin L) :
      (∑ a : Fin q, (-1 : ZMod ℓ) * (if v i = a then 1 else 0) * (if w i = a then 1 else 0)) =
      if v i = w i then -1 else 0 := by simp [mul_ite, eq_comm]
  simp_rw [terms]
  unfold routingDistance
  push_cast
  rw [show (L : ZMod ℓ) = ∑ _ : Fin L, 1 by simp, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp

private abbrev GramIndex (ℓ L q : ℕ) := Unit ⊕ (Fin (ℓ-1) → Match L q)

private def gramWeight (ℓ L q : ℕ) : GramIndex ℓ L q → ZMod ℓ
  | .inl _ => 1
  | .inr t => -(∏ i, matchWeight ℓ L q (t i))

private def gramVector {ℓ L q : ℕ} (v : RoutingLabel L q) : GramIndex ℓ L q → ZMod ℓ
  | .inl _ => 1
  | .inr t => ∏ i, feature v (t i)

private theorem gram_eq_feature_sum {ℓ L q : ℕ} (v w : RoutingLabel L q) :
    routingGram ℓ L q v w = ∑ i, gramWeight ℓ L q i * gramVector v i * gramVector w i := by
  rw [routingGram, distance_eq_sum]
  conv_rhs =>
    rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_unique, gramWeight, gramVector,
      mul_one, neg_mul, ← Finset.prod_mul_distrib, Finset.sum_neg_distrib]
  let t (z : Match L q) := matchWeight ℓ L q z * feature v z * feature w z
  have hs := Fintype.prod_sum (fun (_ : Fin (ℓ-1)) z => t z)
  change 1 - (∑ z, t z)^(ℓ-1) = 1 + -(∑ y : Fin (ℓ-1) → Match L q, ∏ i, t (y i))
  rw [← hs]
  simp [sub_eq_add_neg]

/-- The number of auxiliary directions grows at most as q^(ℓ−1) for fixed
prime and label length. This finite rank bound uses the actual Gram matrix. -/
theorem routingGram_rank_le (ℓ L q : ℕ) [Fact ℓ.Prime] :
    (routingGram ℓ L q).rank ≤ 1 + (1 + L*q) ^ (ℓ-1) := by
  let X : Matrix (RoutingLabel L q) (GramIndex ℓ L q) (ZMod ℓ) :=
    fun v i => gramWeight ℓ L q i * gramVector v i
  let Y : Matrix (GramIndex ℓ L q) (RoutingLabel L q) (ZMod ℓ) :=
    fun i w => gramVector w i
  have h : routingGram ℓ L q = X * Y := by ext v w; exact gram_eq_feature_sum v w
  rw [h]
  apply (Matrix.rank_mul_le_left X Y).trans
  simpa [GramIndex, Match] using X.rank_le_card_width

/-- A nondegenerate diagonal form with nonzero diagonal weights realizes all
the required Gram entries. Each label has norm one, and labels at a distance
nonzero modulo ℓ are orthogonal. -/
theorem exists_routing_gram_vectors (ℓ L q : ℕ) [Fact ℓ.Prime] :
    ∃ D ≤ 1 + (1 + L*q)^(ℓ-1), ∃ a : Fin D → ZMod ℓ, ∃ d : RoutingLabel L q → Fin D → ZMod ℓ,
      (∀ i, a i ≠ 0) ∧ (∀ v w, ∑ i, a i * d v i * d w i = routingGram ℓ L q v w) ∧
      ∀ x : Fin D → ZMod ℓ, (∀ y : Fin D → ZMod ℓ, ∑ i, a i * x i * y i = 0) → x = 0 := by
  classical
  let w := gramWeight ℓ L q
  let J := {i : GramIndex ℓ L q // w i ≠ 0}
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, ?_, fun i => w (e i), fun v i => gramVector v (e i), fun i => (e i).2, ?_, ?_⟩
  · calc
      Fintype.card J ≤ Fintype.card (GramIndex ℓ L q) := Fintype.card_subtype_le _
      _ = _ := by simp [GramIndex, Match]
  · intro v v'
    let f (i : GramIndex ℓ L q) := w i * gramVector v i * gramVector v' i
    have hzero (i : {i : GramIndex ℓ L q // ¬ w i ≠ 0}) : f i.val = 0 := by simp [f, not_ne_iff.mp i.2]
    have hsum := Fintype.sum_subtype_add_sum_subtype (fun i => w i ≠ 0) f
    simp only [hzero, Finset.sum_const_zero, add_zero] at hsum
    exact (e.sum_comp (fun i : J => f i.val)).trans (hsum.trans (gram_eq_feature_sum v v').symm)
  · intro x hx
    funext i
    have h := hx (Pi.single i 1)
    simp [Pi.single_apply, mul_ite] at h
    exact h.resolve_left (e i).2

end FiniteFourier
end LinearAlgebra
end OAI
