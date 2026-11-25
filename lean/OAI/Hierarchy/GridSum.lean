import OAI.Hierarchy.FlatPrices
import OAI.LinearAlgebra.SpectralBooks.PriceOrdinary
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI
/-! # Price of a sum of grid contractions on a common output frame

The output site map may repeat a focus arbitrarily many times. The same
normalizing scalar and the same spectral point then apply to every expanded term. -/

namespace Hierarchy.GridSum

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators Classical

variable {F : Type*} [Field F]

/-- Every nonzero ordinary sum is priced within one selector cost of one of
its nonzero summands, with a joint scale on the distinct occupied output sites. -/
theorem price_sum {I J S : Type} [Fintype I] [Fintype J] [Nontrivial J] [Fintype S]
    {M : Type*} [MetricSpace M] (P : SpectralPlacementPrices F M) (y : J ↪ M)
    (atSite : I → J) {A : I → Type} [∀ i, Fintype (A i)]
    (term : S → (∀ i, A i) → F) (nz : ∑ s, term s ≠ 0) :
    ∃ s, term s ≠ 0 ∧
      P.price (⟨A, inferInstance, ∑ t, term t⟩ : Raw I F) (y ∘ atSite) ≤
        P.price (⟨A, inferInstance, term s⟩ : Raw I F) (y ∘ atSite) +
        P.price (Raw.diagonal J F (Fin 2)) y * Real.logb 2 (Fintype.card S) := by
  classical
  let tensor (v : (∀ i, A i) → F) : Raw I F := ⟨A, inferInstance, v⟩
  let B (j : J) := (i : {i : I // atSite i = j}) → A i.1
  let group (v : (∀ i, A i) → F) : ((j : J) → B j) → F := ((tensor v).group atSite).coeff
  have sums : (∑ s, group (term s)) = group (∑ s, term s) := by
    funext x
    let decode (y : (j : J) → B j) (i : I) := y (atSite i) ⟨i,rfl⟩
    change (∑ s, fun y => term s (decode y)) x = (∑ s, term s) (decode x)
    exact (Finset.sum_apply x Finset.univ (fun s y => term s (decode y))).trans
      (Finset.sum_apply (decode x) Finset.univ term).symm
  have transport (v : (∀ i, A i) → F) : group v ≠ 0 ↔ v ≠ 0 :=
    (tensor v).group_ne_zero_iff atSite
  obtain ⟨φ, hc, prices⟩ := P.normalized_group y
  obtain ⟨s, hs, bound⟩ := ordinary_sum_logb_le (A:=B) φ (fun s => group (term s))
    (sums ▸ ((transport _).2 nz)) hc.le
  rw [sums] at bound
  refine ⟨s, (transport _).1 hs, ?_⟩
  change P.price (tensor (∑ t, term t)) (y ∘ atSite) ≤ P.price (tensor (term s)) (y ∘ atSite) + _
  rw [prices atSite (tensor (∑ t, term t)) nz, prices atSite (tensor (term s)) ((transport _).1 hs)]
  exact bound

/-- The sharper ordinary-sum inequality used by lens reuse prices each
nonzero summand at its own cost. This form allows arbitrary real upper
bounds on zero summands. -/
theorem value_sum {I J S : Type} [Fintype I] [Fintype J] [Nontrivial J] [Fintype S]
    {M : Type*} [MetricSpace M] (P : SpectralPlacementPrices F M) (y : J ↪ M)
    (atSite : I → J) {A : I → Type} [∀ i, Fintype (A i)]
    (term : S → (∀ i, A i) → F) (nz : ∑ s, term s ≠ 0) (cost : S → ℝ)
    (bound : ∀ s, term s ≠ 0 →
      P.price (⟨A, inferInstance, term s⟩ : Raw I F) (y ∘ atSite) ≤ cost s) :
    let c := P.price (Raw.diagonal J F (Fin 2)) y
    (2:ℝ)^((P.price (⟨A, inferInstance, ∑ s, term s⟩ : Raw I F) (y ∘ atSite))/c)
      ≤ ∑ s, (2:ℝ)^(cost s/c) := by
  classical
  let tensor (v : (∀ i, A i) → F) : Raw I F := ⟨A, inferInstance, v⟩
  let B (j : J) := (i : {i : I // atSite i = j}) → A i.1
  let group (v : (∀ i, A i) → F) : ((j : J) → B j) → F := ((tensor v).group atSite).coeff
  let c := P.price (Raw.diagonal J F (Fin 2)) y
  have sums : (∑ s, group (term s)) = group (∑ s, term s) := by
    funext x
    let decode (y : (j : J) → B j) (i : I) := y (atSite i) ⟨i,rfl⟩
    change (∑ s, fun y => term s (decode y)) x = (∑ s, term s) (decode x)
    exact (Finset.sum_apply x Finset.univ (fun s y => term s (decode y))).trans
      (Finset.sum_apply (decode x) Finset.univ term).symm
  obtain ⟨φ, hc, prices⟩ := P.normalized_group y
  have val_eq (v : (∀ i, A i) → F) (hv : v ≠ 0) :
      (2:ℝ)^((P.price (tensor v) (y ∘ atSite))/c) = (coeffValue φ (group v) : ℝ) := by
    have positive := zero_lt_one.trans_le (coeffValue_one_le φ ((tensor v).group_ne_zero_iff atSite |>.2 hv))
    change (2:ℝ)^((P.price (tensor v) (y ∘ atSite))/c) = _
    rw [prices atSite (tensor v) hv]
    change (2:ℝ)^((c * Real.logb 2 (coeffValue φ (group v) : ℝ))/c) = _
    rw [mul_div_cancel_left₀ _ (ne_of_gt hc)]
    exact Real.rpow_logb (by norm_num) (by norm_num) (NNReal.coe_pos.mpr positive)
  change (2:ℝ)^((P.price (tensor _) (y ∘ atSite))/c) ≤ _
  rw [val_eq _ nz, ← sums]
  have hm := ordinary_sum_value_le φ (fun s => group (term s))
  calc
    (coeffValue φ (∑ s, group (term s)) : ℝ) ≤ ∑ s, (coeffValue φ (group (term s)) : ℝ) := by
      exact_mod_cast hm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : term s = 0
      · have zero : group (term s) = 0 := by rw [hs]; rfl
        simp [zero,Real.rpow_nonneg]
      · rw [← val_eq _ hs]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (div_le_div_of_nonneg_right (bound s hs) hc.le)

/-- At one wiring and one fixed hidden assignment, replacing all its cells
gives one term per nonempty set of errors. -/
theorem expand {C : Type} [Fintype C] (base replacement : C → F) :
    (∏ i, replacement i) - (∏ i, base i) =
      ∑ s : {s : Finset C // s ≠ ∅},
        (∏ i ∈ s.val, (replacement i - base i)) * ∏ i ∈ s.valᶜ, base i := by
  classical
  let t (s : Finset C) :=
    (∏ i ∈ s, (replacement i - base i)) * ∏ i ∈ sᶜ, base i
  have all : ∏ i, replacement i = ∑ s, t s := by
    simpa [t] using (Fintype.prod_add (fun i => replacement i - base i) base)
  rw [Fintype.sum_eq_add_sum_subtype_ne t ∅] at all
  have empty : t ∅ = ∏ i, base i := by simp [t]
  rw [empty] at all
  exact sub_eq_iff_eq_add'.2 all

/-- The contraction of one selector with a common arrangement of shared wire bits.
The constant factors include free equality passages and local pin indicators. -/
def contraction {C H : Type} [Fintype C] [Fintype H] (wire : H → F)
    (cell : H → C → F) : F := ∑ h, wire h * ∏ i, cell h i

theorem contraction_difference {C H : Type} [Fintype C] [Fintype H] (wire : H → F)
    (base replacement : H → C → F) :
    contraction wire replacement - contraction wire base =
      ∑ s : {s : Finset C // s ≠ ∅}, ∑ h, wire h *
        ((∏ i ∈ s.val, (replacement h i - base h i)) * ∏ i ∈ s.valᶜ, base h i) := by
  classical
  unfold contraction
  rw [←Finset.sum_sub_distrib, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [←mul_sub, expand, Finset.mul_sum]

end Hierarchy.GridSum

end OAI
