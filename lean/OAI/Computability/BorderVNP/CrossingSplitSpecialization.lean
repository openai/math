import OAI.Computability.BorderVNP.SignedFamily
import OAI.Computability.VPVNP.Circuits
import OAI.Computability.VPVNP.BalancedCoefficients

/-!
# The one-hot specialization of the signed universal polynomial

Section 4.3 fixes the program, data, and padding bits. Each of the remaining
bits belongs to a row and represents one possible value of that row's index.
Specializing the zero-bit variables to one and the one-bit variables to their
index variables recovers the full set-multilinear form of the signed table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open MvPolynomial VPVNP
open scoped Classical

variable {n : ℕ} {P I J : Type*}

/-- Physical input with the prescribed fixed bits and exactly the chosen bit in each row. -/
noncomputable def oneHotWord (layout : Fin n ≃ P ⊕ (I × J)) (pins : P → Bool)
    (a : I → J) (v : Fin n) : Bool :=
  (layout v).elim pins (fun ij => decide (a ij.1 = ij.2))

/-- One literal projection of the paired bit variables. All fixed bits use the indicator
of their prescribed value. The free alternatives use `1` and `X (i,j)`. -/
def oneHotProjection {R : Type*} [Zero R] [One R]
    (layout : Fin n ≃ P ⊕ (I × J)) (pins : P → Bool) :
    Projection R (Fin n × Bool) (I × J) := fun (v, b) =>
  (layout v).elim (fun u => .inr (if b = pins u then 1 else 0))
    (fun ij => if b then .inl ij else .inr 1)

private theorem oneHotWord_injective (layout : Fin n ≃ P ⊕ (I × J)) (pins : P → Bool) :
    Function.Injective (oneHotWord layout pins) := by
  intro a b hab
  funext i
  simpa [oneHotWord] using congrFun hab (layout.symm (.inr (i, b i)))

private theorem exists_oneHotWord (layout : Fin n ≃ P ⊕ (I × J)) (pins : P → Bool)
    (x : Fin n → Bool) (fixed : ∀ u, x (layout.symm (.inl u)) = pins u)
    (rows : ∀ i, ∃! j, x (layout.symm (.inr (i,j))) = true) :
    ∃ a : I → J, oneHotWord layout pins a = x := by
  choose a htrue huniq using rows
  refine ⟨a, funext fun v => ?_⟩
  obtain ⟨w, rfl⟩ := layout.symm.surjective v
  rcases w with u | ⟨i,j⟩
  · simpa [oneHotWord] using (fixed u).symm
  · apply Bool.eq_iff_iff.mpr
    simp only [oneHotWord, Equiv.apply_symm_apply, Sum.elim_inr, decide_eq_true_eq]
    exact ⟨fun h => h ▸ htrue i, fun h => (huniq i j h).symm⟩

/-- The formal set-multilinear polynomial of a tensor with one index per row. -/
noncomputable def sidePolynomial {R : Type*} [CommSemiring R] [Fintype I] [Fintype J]
    (A : (I → J) → R) : MvPolynomial (I × J) R :=
  ∑ a : I → J, C (A a) * ∏ i, X (i, a i)

private theorem sidePolynomial_monomials {R : Type*} [CommSemiring R] [Fintype I] [Fintype J]
    (A : (I → J) → R) : sidePolynomial A =
      ∑ a, monomial (partyExponent Finset.univ a) (A a) := by
  simp only [sidePolynomial, partyExponent, monomial_sum_index, X]

/-- Every monomial in the support has one factor per group. -/
theorem sidePolynomial_isHomogeneous {R : Type*} [CommSemiring R] [Fintype I] [Fintype J]
    (A : (I → J) → R) : (sidePolynomial A).IsHomogeneous (Fintype.card I) := by
  rw [sidePolynomial_monomials]
  apply IsHomogeneous.sum
  intro a _
  exact isHomogeneous_monomial _ (by simp)

/-- Reading the coefficient of the monomial selected by all parties recovers the tensor entry. -/
theorem coeff_sidePolynomial {R : Type*} [CommSemiring R] [Fintype I] [Fintype J]
    (A : (I → J) → R) (a : I → J) :
    (sidePolynomial A).coeff (partyExponent Finset.univ a) = A a := by
  classical
  have evalExponent (b : I → J) (i : I) (j : J) :
      partyExponent Finset.univ b (i,j) = if b i = j then 1 else 0 := by
    rw [partyExponent, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
    · simp [Finsupp.single_apply]
    · intro i' _ hi
      simp [hi]
    · simp
  have inj : Function.Injective (partyExponent (Finset.univ : Finset I) (J := J)) := by
    intro b c h
    funext i
    simpa [evalExponent] using DFunLike.congr_fun h (i, c i)
  simp [sidePolynomial_monomials, coeff_monomial, inj.eq_iff]

/-- The signed path program's one-hot tests and signed output imply the exact
specialization of equation (2.1) claimed in §4.3, over every coefficient ring. -/
theorem oneHotProjection_Pstar (R : Type*) [CommRing R] [Fintype P] [Fintype I] [Fintype J]
    (layout : Fin n ≃ P ⊕ (I × J)) (pins : P → Bool) (A : (I → J) → ℤ)
    (correct : ∀ a, signedCount (oneHotWord layout pins a) = A a)
    (reject : ∀ x : Fin n → Bool, (∀ u, x (layout.symm (.inl u)) = pins u) →
      (¬ ∀ i, ∃! j, x (layout.symm (.inr (i,j))) = true) → signedCount x = 0) :
    (oneHotProjection (R := R) layout pins).hom (map (Int.castRingHom R) (Pstar n)) =
      sidePolynomial (fun a => (A a : R)) := by
  classical
  let factor (x : Fin n → Bool) (v : Fin n) : MvPolynomial (I × J) R :=
    (oneHotProjection (R := R) layout pins (v, x v)).elim X C
  have product (a : I → J) :
      (∏ v, factor (oneHotWord layout pins a) v) = ∏ i, X (i, a i) := by
    rw [← layout.symm.prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type]
    simp [factor, oneHotProjection, oneHotWord, apply_ite]
  rw [map_Pstar]
  simp only [Projection.hom, pairedPolynomial, map_sum, map_mul, eval₂Hom_C, map_prod,
    eval₂Hom_X']
  change (∑ x, C (signedCount x : R) * ∏ v, factor x v) = _
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (oneHotWord layout pins))),
    Finset.sum_image (oneHotWord_injective layout pins).injOn, sidePolynomial]
  · exact Finset.sum_congr rfl fun a _ => by rw [correct, product]
  · intro x _ hx
    by_cases fixed : ∀ u, x (layout.symm (.inl u)) = pins u
    · have bad : ¬ ∀ i, ∃! j, x (layout.symm (.inr (i,j))) = true := by
        intro good
        obtain ⟨a, ha⟩ := exists_oneHotWord layout pins x fixed good
        exact hx (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩)
      simp [reject x fixed bad]
    · obtain ⟨u, hu⟩ := not_forall.mp fixed
      rw [Finset.prod_eq_zero (Finset.mem_univ (layout.symm (.inl u))) (by
        simp [factor, oneHotProjection, hu]), mul_zero]

end Crossing

end BorderVNP
end Computability
end OAI
