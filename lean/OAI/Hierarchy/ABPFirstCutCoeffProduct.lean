import OAI.Hierarchy.ABPFirstCutCoeff

namespace OAI
/-! # Splitting squarefree coefficients across a formula product

For a fixed assignment, a pair of exponent vectors sums to the slot monomial
exactly when a subset of the slots goes to the first vector and its complement
goes to the second vector.
-/

namespace Hierarchy.ABPFirstCut

open scoped BigOperators Classical

noncomputable section

variable {V : Type} {τ : V → Type} [DecidableEq V]

/-- The selected slots can be recovered from their exponent vector. -/
theorem slotExponent_set_injective (a : ∀ i, τ i) : Function.Injective (slotExponent a) := by
  intro S T eq
  ext i
  have hi := DFunLike.congr_fun eq ⟨i,a i⟩
  clear eq
  by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;> simp_all [slotExponent_apply]

theorem slotExponent_add_sdiff (a : ∀ i, τ i) {S T : Finset V} (h : T ⊆ S) :
    slotExponent a T + slotExponent a (S \ T) = slotExponent a S := by
  rw [add_comm]
  exact Finset.sum_sdiff h

private theorem slotExponent_split_at (a : ∀ i, τ i) (S : Finset V)
    (m n : (Σ i, τ i) →₀ ℕ) (h : m + n = slotExponent a S) (i : V) (t : τ i) :
    let T := S.filter (fun j => m ⟨j,a j⟩ = 1)
    m ⟨i,t⟩ = slotExponent a T ⟨i,t⟩ ∧ n ⟨i,t⟩ = slotExponent a (S \ T) ⟨i,t⟩ := by
  classical
  dsimp only
  have hi := DFunLike.congr_fun h ⟨i,t⟩
  simp only [Finsupp.add_apply, slotExponent_apply] at hi
  by_cases hs : i ∈ S
  · by_cases ht : a i = t
    · subst t
      by_cases hm : m ⟨i,a i⟩ = 1 <;> simp [slotExponent_apply, hs, hm] at hi ⊢ <;> omega
    · simp [hs, ht, slotExponent_apply] at hi ⊢
      omega
  · simp [hs, slotExponent_apply] at hi ⊢
    omega

/-- The antidiagonal of a slot monomial is indexed by subsets of the selected slots. -/
theorem antidiagonal_slotExponent (a : ∀ i, τ i) (S : Finset V) :
    Finset.HasAntidiagonal.antidiagonal (slotExponent a S) =
      S.powerset.image (fun T => (slotExponent a T, slotExponent a (S \ T))) := by
  classical
  ext ⟨m,n⟩
  simp only [Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_image, Finset.mem_powerset]
  constructor
  · intro h
    let T := S.filter (fun j => m ⟨j,a j⟩ = 1)
    refine ⟨T, Finset.filter_subset _ _, Prod.ext ?_ ?_⟩
    · ext ⟨i,t⟩
      exact (slotExponent_split_at a S m n h i t).1.symm
    · ext ⟨i,t⟩
      exact (slotExponent_split_at a S m n h i t).2.symm
  · rintro ⟨T, ht, eq⟩
    have h := slotExponent_add_sdiff a ht
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    exact h

/-- The coefficient of a product at a slot monomial is the sum over all ways to
partition the slots between the two factors. -/
theorem slotCoeff_mul {F : Type*} [Field F] (a : ∀ i, τ i) (S : Finset V)
    (p q : MvPolynomial (Σ i, τ i) F) :
    slotCoeff a S (p * q) = ∑ T ∈ S.powerset, slotCoeff a T p * slotCoeff a (S \ T) q := by
  classical
  rw [slotCoeff, MvPolynomial.coeff_mul, antidiagonal_slotExponent, Finset.sum_image]
  · rfl
  · intro U _ T _ eq
    exact slotExponent_set_injective a (congrArg Prod.fst eq)

end
end Hierarchy.ABPFirstCut

end OAI
