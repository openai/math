import OAI.LinearAlgebra.SpectralBooks.GroupedPower
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Matrix-entry histograms in a power of a restriction

In the `n`th grouped power each local matrix entry appears with an exponent
between `0` and `n`. Grouping by all these exponents simultaneously expresses
the power as a linear combination of restrictions by zero-one matrices.
These matrices and the source tensor are defined over the ground field even
when the original restriction matrices have extension-field entries.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

open scoped Classical

noncomputable section

variable {I K E : Type*} [Fintype I] [Field K] [Field E]
    {A B : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

/-- One multiplicity for each matrix entry at each site. -/
abbrev RestrictionProfile (A B : I → Type*) (n : ℕ) := (Σ i, B i × A i) → Fin (n + 1)

private def localHistogram {n : ℕ} {V : Type*} (w : Fin n → V) (v : V) : Fin (n + 1) :=
  ⟨(Finset.univ.filter (w · = v)).card,
    Nat.lt_succ_of_le (by simpa using Finset.card_filter_le Finset.univ (w · = v))⟩

private theorem prod_histogram {V : Type*} [Fintype V] {n : ℕ} (w : Fin n → V) (f : V → E) :
    ∏ v, f v ^ (localHistogram w v : ℕ) = ∏ j, f (w j) := by
  simpa only [localHistogram, Finset.prod_const] using Finset.prod_fiberwise' Finset.univ w f

private def profileMatrix (n : ℕ) (p : RestrictionProfile A B n) (i : I)
    (b : Fin n → B i) (a : Fin n → A i) : K :=
  if (localHistogram fun j ↦ (b j, a j)) = fun v ↦ p ⟨i, v⟩ then 1 else 0

/-- A ground tensor obtained by restricting `S^n` with local histogram indicators. -/
def profileRestriction (n : ℕ) (S : (∀ i, A i) → K) (p : RestrictionProfile A B n)
    (b : ∀ i, Fin n → B i) : K :=
  ∑ a, groupedPower n S a * ∏ i, profileMatrix n p i (b i) (a i)

theorem profileRestriction_restricts (n : ℕ) (S : (∀ i, A i) → K) (p : RestrictionProfile A B n) :
    Crossing.IsRestriction (profileRestriction n S p) (groupedPower n S) :=
  ⟨profileMatrix n p, fun _ ↦ rfl⟩

omit [∀ i, Fintype (B i)] in
/-- A power of a restriction multiplies the corresponding local matrix entries
across the copies of each leg. -/
private theorem groupedPower_restrict_eq (n : ℕ) (S : (∀ i, A i) → E)
    (T : (∀ i, B i) → E) (M : ∀ i, B i → A i → E)
    (h : ∀ b, T b = ∑ a, S a * ∏ i, M i (b i) (a i)) (b : ∀ i, Fin n → B i) :
    groupedPower n T b = ∑ a, groupedPower n S a * ∏ i, ∏ j, M i (b i j) (a i j) := by
  unfold groupedPower coordinatePower
  simp_rw [h, Fintype.prod_sum]
  apply Fintype.sum_equiv (Equiv.piComm (fun (_ : Fin n) i ↦ A i))
  intro a
  rw [Finset.prod_mul_distrib, Finset.prod_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun j i ↦ M i (b i j) (a j i))]
  rfl

/-- A family independent of the extension and restriction matrices spans all
`n`th powers of restrictions over the extension. -/
theorem groupedPower_mem_span_profileRestrictions [Algebra K E] (n : ℕ)
    (S : (∀ i, A i) → K) {T : (∀ i, B i) → E}
    (h : Crossing.IsRestriction T (fun a ↦ algebraMap K E (S a))) :
    groupedPower n T ∈ Submodule.span E (Set.range (fun p : RestrictionProfile A B n ↦
      fun x ↦ algebraMap K E (profileRestriction n S p x))) := by
  classical
  obtain ⟨M, hM⟩ := h
  let w (p : RestrictionProfile A B n) := ∏ i, ∏ v : B i × A i, M i v.1 v.2 ^ (p ⟨i, v⟩ : ℕ)
  apply (Submodule.mem_span_range_iff_exists_fun E).mpr
  refine ⟨w, ?_⟩
  ext b
  rw [groupedPower_restrict_eq n _ T M hM b]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, profileRestriction,
    map_sum, map_mul, map_prod, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  let p₀ : RestrictionProfile A B n := fun ⟨i,v⟩ ↦ localHistogram (fun j ↦ (b i j, a i j)) v
  have hind (p : RestrictionProfile A B n) :
      (∏ i, algebraMap K E (profileMatrix n p i (b i) (a i))) = if p = p₀ then 1 else 0 := by
    simp only [profileMatrix, apply_ite, map_one, map_zero, Fintype.prod_boole]
    have heq : (∀ i, (localHistogram fun j ↦ (b i j, a i j)) = fun v ↦ p ⟨i, v⟩) ↔ p = p₀ := by
      constructor
      · intro h
        funext ⟨i,v⟩
        exact (congrFun (h i) v).symm
      · rintro rfl i
        rfl
    simp only [heq]
    split <;> simp_all
  simp only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hw : w p₀ = ∏ i, ∏ j, M i (b i j) (a i j) :=
    Finset.prod_congr rfl (fun i _ ↦ prod_histogram (fun j ↦ (b i j, a i j)) (fun v ↦ M i v.1 v.2))
  simp only [hw, groupedPower, coordinatePower, map_prod, mul_comm]

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
