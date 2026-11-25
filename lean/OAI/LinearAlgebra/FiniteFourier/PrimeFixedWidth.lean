import OAI.LinearAlgebra.FiniteFourier.PrimeFullRepair
import OAI.LinearAlgebra.FiniteFourier.PrimeCyclotomicPencil

/-! # A common clock width independent of the coefficient ring

Index clock digits by the entire box of exponent vectors of polynomials of degree
at most `b`. Including unused monomials permits the cycle length, row count and
number of Vandermonde nodes to be chosen before extending the coefficient ring.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open MvPolynomial Matrix

/-- One clock digit for each possible componentwise bounded exponent vector. -/
def primeClockDigits (ℓ m b : ℕ) : ℕ := (b + 1) ^ (m * ℓ)

/-- Number of independent predictor rows in a single label. -/
def primePredictorRows (ℓ m b : ℕ) : ℕ := ℓ ^ m * b ^ primeClockDigits ℓ m b

private def boxExponent {σ : Type*} [Fintype σ] (b : ℕ) :
    (σ → Fin (b+1)) ↪ (σ →₀ ℕ) where
  toFun a := Finsupp.equivFunOnFinite.symm (fun i => (a i).val)
  inj' := by
    intro a a' he
    funext i
    exact Fin.ext (DFunLike.congr_fun he i)

private theorem family_box_factors {σ B R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R] [Nontrivial R]
    {b : ℕ} (hb : 0 < b) (p : B → MvPolynomial σ R) (hp : ∀ v, (p v).totalDegree ≤ b) :
    ∃ f : B → (σ → Fin (b + 1)) → Fin b → MvPolynomial σ R,
      (∀ v a j, (f v a j).totalDegree ≤ 1) ∧ ∀ v, p v = ∑ a, ∏ j, f v a j := by
  classical
  let e := boxExponent (σ := σ) b
  have hs (v : B) : (p v).support ⊆ Finset.univ.map e := by
    intro d hd
    let a (i : σ) : Fin (b+1) := ⟨d i, Nat.lt_succ_of_le
      ((monomial_le_degreeOf i hd).trans ((degreeOf_le_totalDegree (p v) i).trans (hp v)))⟩
    exact Finset.mem_map.mpr ⟨a, Finset.mem_univ _, Finsupp.ext fun _ => rfl⟩
  have hex (v : B) (a : σ → Fin (b+1)) :
      ∃ g : Fin b → MvPolynomial σ R, (∀ j, (g j).totalDegree ≤ 1) ∧
        monomial (e a) ((p v).coeff (e a)) = ∏ j, g j := by
    by_cases ha : e a ∈ (p v).support
    · exact monomial_eq_prod_affine _ hb ((le_totalDegree ha).trans (hp v))
    · refine ⟨fun _ => 0, by simp, ?_⟩
      simp [notMem_support_iff.mp ha, hb.ne']
  choose f hf he using hex
  refine ⟨f, hf, fun v => ?_⟩
  simp_rw [← he]
  calc
    p v = ∑ d ∈ (p v).support, monomial d ((p v).coeff d) := (p v).as_sum
    _ = ∑ d ∈ Finset.univ.map e, monomial d ((p v).coeff d) :=
      Finset.sum_subset (hs v) fun _ _ hd => by simp [notMem_support_iff.mp hd]
    _ = _ := Finset.sum_map ..

/-- Uniform size version of the simultaneous matrix-root identity. -/
theorem exists_fixed_width_matrix_roots {ℓ m b : ℕ} [NeZero ℓ] [NeZero b]
    {R B : Type*} [CommRing R] [Nontrivial R] {ξ : R}
    (hpow : ξ ^ b = 1) (hu : ∀ k, 0 < k → k < b → IsUnit (ξ^k-1)) (p : B → MvPolynomial (Fin m × ZMod ℓ) R)
    (hp : ∀ v, (p v).totalDegree ≤ b) :
    ∃ L : B → Matrix (Fin (primeClockDigits ℓ m b) → Fin b)
        (Fin (primeClockDigits ℓ m b) → Fin b) (MvPolynomial (Fin m × ZMod ℓ) R),
      (∀ v x y, ((L v) x y).totalDegree ≤ 1) ∧ ∀ v, (L v) ^ b = p v • 1 := by
  classical
  obtain ⟨g, hdeg, hsum⟩ := family_box_factors (NeZero.pos b) p hp
  let e : ((Fin m × ZMod ℓ) → Fin (b+1)) ≃ Fin (primeClockDigits ℓ m b) :=
    Fintype.equivFinOfCardEq (by simp [primeClockDigits])
  let f (v : B) (i : Fin (primeClockDigits ℓ m b)) := g v (e.symm i)
  refine ⟨fun v => ∑ i, qClockTerm (C ξ) (f v) i, ?_, ?_⟩
  · intro v x y
    dsimp only
    rw [Matrix.sum_apply x y _ (fun i => qClockTerm (C ξ) (f v) i)]
    exact totalDegree_finsetSum_le fun i _ =>
      qClockTerm_affine ξ (f v) (fun k j => hdeg v (e.symm k) j) i x y
  · intro v
    have hp' : (C ξ : MvPolynomial (Fin m × ZMod ℓ) R)^b = 1 := by rw [← map_pow, hpow, map_one]
    have hu' (k : ℕ) (hk : 0 < k) (hb : k < b) :
        IsUnit ((C ξ : MvPolynomial (Fin m × ZMod ℓ) R)^k-1) := by
      simpa only [map_sub, map_pow, map_one] using (hu k hk hb).map (C (σ := Fin m × ZMod ℓ))
    rw [qClock_sum_pow_of_units hp' hu' (f v), hsum v]
    congr 1
    exact e.symm.sum_comp (fun a => ∏ j, g v a j)

end

end

end FiniteFourier
end LinearAlgebra
end OAI
