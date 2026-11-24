import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Products of old and added generators in the exact extension proof

The monomials in Theorem 2.4 have arbitrarily many embedded old factors
and either one star generator or two split wires. Multiplicativity folds
all the old factors into one embedded product. The common-exponent
monomial retains both required wires with equal multiplicities.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

variable {A B ι E : Type*} [CommMonoid A] [CommMonoid B]

/-- Separate the finite product into its old factors and its added factors.
The two groups can have different, individually prescribed exponents. -/
theorem fold_generatorProduct (φ : A →* B) (old : ι → A) (extra : E → B)
    (s : Finset (ι ⊕ E)) (p : ι ⊕ E → ℕ) :
    ∏ i ∈ s, (Sum.elim (φ ∘ old) extra i) ^ p i =
      φ (∏ j ∈ s.toLeft, old j ^ p (.inl j)) * ∏ j ∈ s.toRight, extra j ^ p (.inr j) := by
  rw [Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
  simp only [Sum.elim_inl, Function.comp_apply, Sum.elim_inr, map_prod, map_pow]

/-- A monomial of finite support contains every extra generator to its
prescribed power. Exponents outside its support contribute units. -/
theorem fold_generatorMonomial [Fintype E] (φ : A →* B) (old : ι → A) (extra : E → B)
    (d : (ι ⊕ E) →₀ ℕ) :
    d.prod (fun i n ↦ (Sum.elim (φ ∘ old) extra i) ^ n) =
      φ (∏ j ∈ d.support.toLeft, old j ^ d (.inl j)) * ∏ j, extra j ^ d (.inr j) := by
  classical
  rw [Finsupp.prod, fold_generatorProduct]
  congr 1
  apply Finset.prod_subset (Finset.subset_univ _)
  intro j _ hj
  have h : d (.inr j) = 0 := Finsupp.notMem_support_iff.mp (fun h ↦ hj (Finset.mem_toRight.mpr h))
  simp [h]

/-- If all extra generators are required, each appears exactly `e` times
in the reference monomial. -/
theorem fold_generatorBalanced [Fintype E] (φ : A →* B) (old : ι → A) (extra : E → B)
    (s : Finset (ι ⊕ E)) (e : ℕ) (hs : ∀ j, Sum.inr j ∈ s) :
    ∏ i ∈ s, (Sum.elim (φ ∘ old) extra i) ^ e =
      φ (∏ j ∈ s.toLeft, old j ^ e) * ∏ j, extra j ^ e := by
  have hall : s.toRight = Finset.univ :=
    Finset.eq_univ_of_forall (fun j ↦ Finset.mem_toRight.mpr (hs j))
  simpa only [hall] using fold_generatorProduct φ old extra s (fun _ ↦ e)

/-- One star generator in an arbitrary monomial. -/
theorem fold_starMonomial (φ : A →* B) (old : ι → A) (S : B) (d : (ι ⊕ Unit) →₀ ℕ) :
    d.prod (fun i n ↦ (Sum.elim (φ ∘ old) (fun _ ↦ S) i) ^ n) =
      φ (∏ j ∈ d.support.toLeft, old j ^ d (.inl j)) * S ^ d (.inr ()) := by
  simpa only [Fintype.prod_unique] using fold_generatorMonomial φ old (fun _ ↦ S) d

/-- One required star generator in the reference monomial. -/
theorem fold_starBalanced (φ : A →* B) (old : ι → A) (S : B)
    (s : Finset (ι ⊕ Unit)) (e : ℕ) (hs : Sum.inr () ∈ s) :
    ∏ i ∈ s, (Sum.elim (φ ∘ old) (fun _ ↦ S) i) ^ e =
      φ (∏ j ∈ s.toLeft, old j ^ e) * S ^ e := by
  simpa only [Fintype.prod_unique] using
    fold_generatorBalanced φ old (fun _ ↦ S) s e (fun _ ↦ hs)

/-- The two split-wire multiplicities in an arbitrary monomial. -/
theorem fold_splitMonomial (φ : A →* B) (old : ι → A) (wire : Bool → B)
    (d : (ι ⊕ Bool) →₀ ℕ) :
    d.prod (fun i n ↦ (Sum.elim (φ ∘ old) wire i) ^ n) =
      φ (∏ j ∈ d.support.toLeft, old j ^ d (.inl j)) *
        (wire false ^ d (.inr false) * wire true ^ d (.inr true)) := by
  rw [fold_generatorMonomial, Fintype.prod_bool, mul_comm (wire true ^ _)]

/-- The two required split wires occur with equal multiplicity in the
reference monomial, so its center can contract to the full identity. -/
theorem fold_splitBalanced (φ : A →* B) (old : ι → A) (wire : Bool → B)
    (s : Finset (ι ⊕ Bool)) (e : ℕ) (hs : ∀ j : Bool, Sum.inr j ∈ s) :
    ∏ i ∈ s, (Sum.elim (φ ∘ old) wire i) ^ e =
      φ (∏ j ∈ s.toLeft, old j ^ e) * (wire false ^ e * wire true ^ e) := by
  rw [fold_generatorBalanced φ old wire s e hs, Fintype.prod_bool, mul_comm (wire true ^ _)]

end Spectral

end VPVNP
end Computability
end OAI
