import OAI.Computability.VPVNP.ParseHistogram
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi

/-!
# The histogram coefficient of a primed pair

For fixed exterior cut bits, `input s v` is the primed bit string at site `v`
when the internal shared bits have assignment `s`. No machine-transcript
validation is imposed on that assignment. Section 9.3 expands the product
of all these sites' label queries over the integers. Its coefficient counts
joint choices of internal bits, ordered parses, and leaf bijections with the
prescribed histogram of terminal and binary productions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairCoefficient

open MvPolynomial ParseGrammar
open scoped Classical

variable {Internal Site H : Type*} {n m : ℕ} [Fintype Internal] [Fintype Site] [Fintype H]

/-- Each site makes its own ordered parse and its own assignment of its
terminal occurrences to the distinct queried positions. -/
abbrev Choices (H : Type*) (d : Fin n) (input : Internal → Site → Fin m → Bool) :=
  (s : Internal) × ((v : Site) → ParseChoice H d (input s v))

/-- All occurrences of one grammar label at all sites of the pair share one counter. -/
noncomputable def jointHistogram (d : Fin n) (h : H) (input : Internal → Site → Fin m → Bool)
    (c : Choices H d input) : GrammarLabel (Fin m × Bool) H n →₀ ℕ :=
  ∑ v, histogram d h (c.2 v).1

/-- The polynomial `F` in equation (9.4), before assigning scalars to any labels. -/
noncomputable def jointPolynomial (d : Fin n) (h : H) (input : Internal → Site → Fin m → Bool) :
    MvPolynomial (GrammarLabel (Fin m × Bool) H n) ℤ :=
  ∑ s, ∏ v, labelQuery d h (input s v)

/-- Fully expand the product over all sites before grouping equal label monomials. -/
theorem jointPolynomial_eq_sum (d : Fin n) (h : H) (input : Internal → Site → Fin m → Bool) :
    jointPolynomial d h input =
      ∑ c : Choices H d input, monomial (jointHistogram d h input c) 1 := by
  rw [jointPolynomial, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [labelQuery_eq_sum_histogram]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro choices _
  exact (monomial_sum_one _ _).symm

/-- Exact multiplicity of each histogram. The integer coefficient includes
every choice of internal bits and every tuple of local parses with this histogram. -/
theorem coeff_eq_count (d : Fin n) (h : H) (input : Internal → Site → Fin m → Bool)
    (μ : GrammarLabel (Fin m × Bool) H n →₀ ℕ) :
    (jointPolynomial d h input).coeff μ =
      (Fintype.card {c : Choices H d input // jointHistogram d h input c = μ} : ℤ) := by
  rw [jointPolynomial_eq_sum, coeff_sum]
  simp only [coeff_monomial, Fintype.card_subtype]
  convert! Finset.sum_boole (R := ℤ) (fun c : Choices H d input => jointHistogram d h input c = μ) Finset.univ using 2
  split_ifs <;> rfl

omit [Fintype Internal] in
/-- A parse uses one label at each terminal and one at each binary node.
This gives the component bound used for the `2r`-bit nominations in (9.4). -/
theorem histogram_component_le (d : Fin n) (h : H) (input : Internal → Site → Fin m → Bool)
    (c : Choices H d input) (a : GrammarLabel (Fin m × Bool) H n) :
    jointHistogram d h input c a ≤ Fintype.card Site * (2 * d.val + 1) := by
  rw [jointHistogram, Finsupp.finsetSum_apply]
  calc
    _ ≤ ∑ _v : Site, (2 * d.val + 1) := by
      apply Finset.sum_le_sum
      intro v _
      rw [← histogram_sum d h (c.2 v).1]
      exact Finset.single_le_sum (fun i _ => Nat.zero_le (histogram d h (c.2 v).1 i))
        (Finset.mem_univ a)
    _ = _ := by simp

/-- For two groups of `R = 2^r` sites, the paper's `2r`-bit counters cover
all histograms whenever `4n ≤ R` and the layer has degree `n`. -/
theorem pair_counter_capacity (r n : ℕ) (hn : 0 < n) (hR : 4 * n ≤ 2 ^ r) :
    (2 * 2 ^ r) * (2 * (n - 1) + 1) < 2 ^ (2 * r) := by
  have h : 2 * (2 * (n - 1) + 1) < 2 ^ r := by omega
  calc
    _ = 2 ^ r * (2 * (2 * (n - 1) + 1)) := by ac_rfl
    _ < 2 ^ r * 2 ^ r := Nat.mul_lt_mul_of_pos_left h (Nat.two_pow_pos r)
    _ = _ := by rw [two_mul, pow_add]

/-- Nominate every histogram whose individual counters fit in the chosen
fixed width. Evaluating the primed pair polynomial over any field or
commutative ring sums its monomials with the number of matching parses. -/
theorem evaluate_by_nominations {A : Type*} [CommRing A]
    [DecidableEq (GrammarLabel (Fin m × Bool) H n)]
    (d : Fin n) (h : H) (input : Internal → Site → Fin m → Bool)
    (value : GrammarLabel (Fin m × Bool) H n → A) (w : ℕ)
    (hfit : Fintype.card Site * (2 * d.val + 1) < 2 ^ w) :
    eval₂Hom (Int.castRingHom A) value (jointPolynomial d h input) =
      ∑ μ : GrammarLabel (Fin m × Bool) H n → Fin (2 ^ w), (∏ a, value a ^ (μ a).val) *
        (Fintype.card {c : Choices H d input // ∀ a, jointHistogram d h input c a = (μ a).val} : A) := by
  let nominate (c : Choices H d input) (a : GrammarLabel (Fin m × Bool) H n) : Fin (2 ^ w) :=
    ⟨jointHistogram d h input c a, (histogram_component_le d h input c a).trans_lt hfit⟩
  let weight (μ : GrammarLabel (Fin m × Bool) H n → Fin (2 ^ w)) := ∏ a, value a ^ (μ a).val
  rw [jointPolynomial_eq_sum, map_sum]
  calc
    _ = ∑ c : Choices H d input, weight (nominate c) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [eval₂Hom_monomial, map_one, one_mul, Finsupp.prod_fintype]
      simp
    _ = ∑ μ, ∑ _c : {c : Choices H d input // nominate c = μ}, weight μ :=
      (Fintype.sum_fiberwise' nominate weight).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro μ _
      have heq (c : Choices H d input) : nominate c = μ ↔
          ∀ a, jointHistogram d h input c a = (μ a).val := by
        constructor
        · intro hnom a
          exact congrArg Fin.val (congrFun hnom a)
        · intro hnom
          exact funext (fun a => Fin.ext (hnom a))
      simp [weight, Fintype.card_subtype, heq, nsmul_eq_mul, mul_comm]

end PairCoefficient

end VPVNP
end Computability
end OAI
