import OAI.Computability.BorderVNP.Model
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Tensor powers at a point in a Zariski closure

Lemma 3.3 expresses a power of a limiting tensor as an exact linear combination of
powers of attainable tensors. The bound on the number of terms counts multisets of
coordinates. It requires neither a division by a factorial nor an infinite base field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open MvPolynomial
open scoped BigOperators

variable {ι K : Type*} [Field K]

/-- The coordinates of the ordered tensor power of a vector in a product basis. -/
def coordinatePower (t : ℕ) (x : ι → K) (w : Fin t → ι) : K :=
  ∏ i, x (w i)

/-- Each coordinate of the tensor-power map is a monomial. -/
theorem coordinatePower_eval (t : ℕ) (x : ι → K) (w : Fin t → ι) :
    eval x (∏ i, (X (w i) : MvPolynomial ι K)) = coordinatePower t x w := by
  simp [coordinatePower]

variable [Fintype ι]

/-- A linear functional on a finite coordinate space is represented by a linear polynomial. -/
private theorem polynomial_of_linear (f : (ι → K) →ₗ[K] K) :
    ∃ q : MvPolynomial ι K, ∀ x : ι → K, eval x q = f x := by
  classical
  refine ⟨∑ i, X i * C (f (Pi.single i 1)), fun x => ?_⟩
  simp only [map_sum, map_mul, eval_X, eval_C]
  conv_rhs => rw [← Finset.univ_sum_single x, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_eq_mul, ← map_smul, ← Pi.single_smul']
  simp

/-- Linear equations cut out the span of any subset of a finite coordinate space. -/
theorem imageClosure_subset_span (S : Set (ι → K)) :
    imageClosure S ⊆ (Submodule.span K S : Set (ι → K)) := by
  intro x hx
  by_contra h
  obtain ⟨f, hfx, hS⟩ := Submodule.exists_le_ker_of_notMem h
  obtain ⟨q, hq⟩ := polynomial_of_linear f
  exact hfx ((hq x).symm.trans (hx q fun y hy =>
    (hq y).trans (hS (Submodule.subset_span hy))))

/-- All powers of a point in the closure lie in the span of actual powers, even in
positive characteristic. -/
theorem coordinatePower_mem_span {S : Set (ι → K)} {x : ι → K}
    (hx : x ∈ imageClosure S) (t : ℕ) :
    coordinatePower t x ∈ Submodule.span K (coordinatePower t '' S) := by
  classical
  apply imageClosure_subset_span
  simpa only [coordinatePower_eval] using
    imageClosure_polynomial hx (fun w : Fin t → ι => ∏ i, X (w i))

/-- The dimension of the span of actual powers is bounded by the number of degree-`t`
monomials in the ambient coordinates. -/
theorem finrank_powerSpan_le (S : Set (ι → K)) (t : ℕ) :
    Module.finrank K (Submodule.span K (coordinatePower t '' S)) ≤
      (Fintype.card ι + t - 1).choose t := by
  classical
  let wordMultiset (w : Fin t → ι) : Sym ι t := ⟨List.ofFn w, by simp⟩
  let lift := LinearMap.funLeft K K wordMultiset
  have h : Submodule.span K (coordinatePower t '' S) ≤ LinearMap.range lift := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, _, rfl⟩
    refine ⟨fun m : Sym ι t => (m.val.map x).prod, ?_⟩
    funext w
    change ((↑(List.ofFn w) : Multiset ι).map x).prod = ∏ i, x (w i)
    simp [Function.comp_def, Fin.prod_ofFn]
  calc
    _ ≤ Module.finrank K (LinearMap.range lift) := Submodule.finrank_mono h
    _ ≤ Module.finrank K (Sym ι t → K) := lift.finrank_range_le
    _ = _ := (Module.finrank_pi K).trans (Sym.card_sym_eq_choose t)

/-- Choose a basis from the attainable powers, and express the limiting power in that basis. -/
theorem coordinatePower_interpolate {S : Set (ι → K)} {x : ι → K}
    (hx : x ∈ imageClosure S) (t : ℕ) :
    ∃ b ≤ (Fintype.card ι + t - 1).choose t, ∃ a : Fin b → ι → K, ∃ c : Fin b → K,
      (∀ i, a i ∈ S) ∧ coordinatePower t x = ∑ i, c i • coordinatePower t (a i) := by
  classical
  obtain ⟨f, hf, hspan, _⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (coordinatePower t '' S)
  choose a ha he using hf
  have h := coordinatePower_mem_span hx t
  rw [← hspan, Submodule.mem_span_range_iff_exists_fun K] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨_, finrank_powerSpan_le S t, a, c, ha, ?_⟩
  simpa only [he] using hc.symm

/-- Expanding the attainable sums in Lemma 3.3 gives at most
`choose(v + t - 1, t) * L ^ t` ordinary product terms. Each outer index selects
an actual parameter assignment and each inner word selects its `t` network factors. -/
theorem interpolate_network_sums {α : Type*} {L : ℕ} (term : α → Fin L → ι → K)
    {x : ι → K} (hx : x ∈ imageClosure (Set.range fun p => ∑ i, term p i)) (t : ℕ) :
    ∃ b ≤ (Fintype.card ι + t - 1).choose t, ∃ p : Fin b → α, ∃ c : Fin b → K,
      ∀ w : Fin t → ι, coordinatePower t x w =
        ∑ i, ∑ word : Fin t → Fin L, c i * ∏ j, term (p i) (word j) (w j) := by
  classical
  obtain ⟨b, hb, a, c, ha, hsum⟩ := coordinatePower_interpolate hx t
  choose p hp using ha
  refine ⟨b, hb, p, c, fun w => ?_⟩
  have hw := congrFun hsum w
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordinatePower, ← hp] at hw
  simpa only [coordinatePower, Finset.sum_apply, Fintype.prod_sum, Finset.mul_sum] using hw

end Crossing

end BorderVNP
end Computability
end OAI
