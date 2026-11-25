import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.BigOperators

/-! # Multiplication between the two jet specializations

The descent computes a product at the long jet at zero and reads it at the short jet at one.
The structure constants are products over the active axes. A binomial wrap contributes a
linear polynomial, and a simultaneous quadratic reduction contributes a second linear factor.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The jet algebra in the parameter at an endpoint. -/
abbrev Jet (R : Type*) [CommRing R] (h : ℕ) := AdjoinRoot ((X : R[X]) ^ h)

/-- Specialization at (t=a+z) in the length-(h) jet. -/
noncomputable def specialize (a : R) (h : ℕ) : R[X] →ₐ[R] Jet R h :=
  (aeval (AdjoinRoot.root ((X : R[X]) ^ h))).comp (taylorAlgHom a)

/-- Read a jet as a polynomial in the common parameter centered at (a). -/
noncomputable def liftJet (a : R) (h : ℕ) : Jet R h →ₗ[R] R[X] :=
  (taylor (-a)).comp (AdjoinRoot.modByMonicHom (monic_X_pow h))

theorem specialize_liftJet (a : R) (h : ℕ) (v : Jet R h) :
    specialize a h (liftJet a h v) = v := by
  change aeval _ (taylor a (taylor (-a) _)) = _
  rw [taylor_taylor, add_neg_cancel, taylor_zero, AdjoinRoot.aeval_eq]
  exact AdjoinRoot.mk_leftInverse (monic_X_pow h) v

theorem natDegree_liftJet_lt (a : R) {h : ℕ} (hh : 0 < h) (v : Jet R h) :
    (liftJet a h v).natDegree < h := by
  cases subsingleton_or_nontrivial R with
  | inl _ => simpa [Subsingleton.elim (liftJet a h v) 0] using hh
  | inr _ =>
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective v
    simp only [liftJet, LinearMap.comp_apply, natDegree_taylor, AdjoinRoot.modByMonicHom_mk]
    by_cases h0 : p %ₘ (X : R[X]) ^ h = 0
    · simpa [h0]
    · exact (natDegree_lt_iff_degree_lt h0).mpr (by
        simpa using degree_modByMonic_lt p (monic_X_pow h))

theorem liftJet_specialize (a : R) {h : ℕ} (p : R[X]) (hp : p.natDegree < h) :
    liftJet a h (specialize a h p) = p := by
  nontriviality R
  change taylor (-a) (AdjoinRoot.modByMonicHom _ (aeval _ (taylor a p))) = p
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.modByMonicHom_mk]
  rw [(modByMonic_eq_self_iff (monic_X_pow h)).mpr, taylor_taylor]
  · simp
  · rw [degree_taylor, degree_X_pow]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hp)

/-- The linear recovery map between the two endpoints. -/
noncomputable def readAtOne (H r : ℕ) : Jet R H →ₗ[R] Jet R r :=
  (specialize (1 : R) r).toLinearMap.comp (liftJet 0 H)

theorem readAtOne_specialize_zero {H : ℕ} (r : ℕ) (p : R[X]) (hp : p.natDegree < H) :
    readAtOne H r (specialize 0 H p) = specialize 1 r p := by
  simp [readAtOne, liftJet_specialize _ _ hp]

/-- Ordinary structure-constant multiplication in a finite basis. -/
def multiply {ι A : Type*} [Fintype ι] [CommSemiring A] (c : ι → ι → ι → A)
    (x y : ι → A) (k : ι) : A :=
  ∑ i, ∑ j, x i * y j * c i j k

theorem map_multiply {ι A B : Type*} [Fintype ι] [CommSemiring A] [CommSemiring B]
    (φ : A →+* B) (c : ι → ι → ι → A) (x y : ι → A) (k : ι) :
    φ (multiply c x y k) = multiply (fun i j k => φ (c i j k)) (φ ∘ x) (φ ∘ y) k := by
  simp [multiply]

variable {ι : Type*} [Fintype ι]

/-- Each coefficient of the lifted product has degree at most the sum of the two operand
degree bounds and the degree bound on a reduced basis product. -/
theorem natDegree_multiply_le (c : ι → ι → ι → R[X]) (x y : ι → R[X]) (k : ι)
    {a b D : ℕ} (hx : ∀ i, (x i).natDegree ≤ a) (hy : ∀ j, (y j).natDegree ≤ b)
    (hc : ∀ i j, (c i j k).natDegree ≤ D) :
    (multiply c x y k).natDegree ≤ a + b + D := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_mul_le).trans (Nat.add_le_add
    (natDegree_mul_le.trans (Nat.add_le_add (hx i) (hy j))) (hc i j))

/-- Applying the same lift to both inputs, multiplying in the long jet, and reading at one
gives the product at one.  The precision (2r+D) suffices when each structure constant has
degree at most (D). -/
theorem recover_multiply (r D : ℕ) (hr : 0 < r) (c : ι → ι → ι → R[X])
    (hc : ∀ i j k, (c i j k).natDegree ≤ D) (x y : ι → Jet R r) (k : ι) :
    let H := 2 * r + D
    let input := specialize (0 : R) H ∘ liftJet 1 r
    readAtOne H r (multiply (fun i j k => specialize 0 H (c i j k)) (input ∘ x) (input ∘ y) k)
      = multiply (fun i j k => specialize 1 r (c i j k)) x y k := by
  dsimp only
  let x' := liftJet (1 : R) r ∘ x
  let y' := liftJet (1 : R) r ∘ y
  have hdeg : (multiply c x' y' k).natDegree ≤ (r - 1) + (r - 1) + D :=
    natDegree_multiply_le c x' y' k
      (fun i => Nat.le_pred_of_lt (natDegree_liftJet_lt _ hr _))
      (fun j => Nat.le_pred_of_lt (natDegree_liftJet_lt _ hr _)) (fun i j => hc i j k)
  change readAtOne _ _ (multiply _ (specialize 0 _ ∘ x') (specialize 0 _ ∘ y') _) = _
  calc
    _ = readAtOne _ _ (specialize 0 (2 * r + D) (multiply c x' y' k)) :=
      congrArg (readAtOne _ _) (map_multiply (specialize 0 (2*r+D)).toRingHom c x' y' k).symm
    _ = specialize 1 r (multiply c x' y' k) := readAtOne_specialize_zero _ _ (by omega)
    _ = _ := by simp [multiply, x', y', specialize_liftJet]


/-- The binomial on an active axis is `Y^m = f(t)`. -/
noncomputable def binomial (β : R) : R[X] := 1 + C (β - 1) * X

/-- Coefficients on `1,U` after the reduction `U² = -U - ρt`. -/
noncomputable def quadraticCoeff (ρ : R) (a b k : Fin 2) : R[X] :=
  if a.val + b.val < 2 then (if k.val = a.val + b.val then 1 else 0)
  else if k = 0 then -(C ρ * X) else -1

/-- Coefficient on `Y^k` after the binomial reduction. Two basis inputs wrap at most once. -/
noncomputable def binomialCoeff (β : R) {m : ℕ} (a b k : Fin m) : R[X] :=
  if k.val = (a.val + b.val) % m then (if a.val + b.val < m then 1 else binomial β)
  else 0

private theorem natDegree_binomial (β : R) : (binomial β).natDegree ≤ 1 := by
  exact natDegree_add_le_of_degree_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le)

theorem natDegree_quadraticCoeff (ρ : R) (a b k : Fin 2) :
    (quadraticCoeff ρ a b k).natDegree ≤ 1 := by
  unfold quadraticCoeff
  split_ifs <;> simp
  exact (natDegree_C_mul_le _ _).trans natDegree_X_le

theorem natDegree_binomialCoeff (β : R) {m : ℕ} (a b k : Fin m) :
    (binomialCoeff β a b k).natDegree ≤ 1 := by
  unfold binomialCoeff
  split_ifs <;> simp [natDegree_binomial]

variable {A : Type*} [CommRing A]

theorem quadratic_normal_form (φ : R[X] →+* A) (ρ : R) (u : A)
    (hu : u ^ 2 = -u - φ (C ρ * X)) (a b : Fin 2) :
    ∑ k : Fin 2, φ (quadraticCoeff ρ a b k) * u ^ k.val = u ^ a.val * u ^ b.val := by
  fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two, quadraticCoeff, ← pow_two, hu]
  ring

theorem binomial_normal_form (φ : R[X] →+* A) (β : R) {m : ℕ} (y : A)
    (hy : y ^ m = φ (binomial β)) (a b : Fin m) :
    ∑ k : Fin m, φ (binomialCoeff β a b k) * y ^ k.val = y ^ a.val * y ^ b.val := by
  have ha := a.isLt
  have hb := b.isLt
  let k : Fin m := ⟨(a.val + b.val) % m, Nat.mod_lt _ (by omega)⟩
  have he (j : Fin m) : j.val = (a.val + b.val) % m ↔ j = k := (Fin.ext_iff (a := j) (b := k)).symm
  simp only [binomialCoeff, he, apply_ite φ, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, ← pow_add]
  by_cases hab : a.val + b.val < m
  · simp [hab, k, Nat.mod_eq_of_lt]
  · rw [ite_eq_right hab, ← hy, ← pow_add]
    congr 1
    change m + ((a.val + b.val) % m) = a.val + b.val
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The coefficient in a product of basis monomials on the active axes. The quadratic and
binomial reductions are independent on each axis. -/
noncomputable def integralCoeff {σ : Type*} [Fintype σ] (ρ β : σ → R) (m : σ → ℕ)
    (a b k : ∀ i, Fin 2 × Fin (m i)) : R[X] :=
  ∏ i, quadraticCoeff (ρ i) (a i).1 (b i).1 (k i).1 *
    binomialCoeff (β i) (a i).2 (b i).2 (k i).2

theorem natDegree_integralCoeff {σ : Type*} [Fintype σ] (ρ β : σ → R) (m : σ → ℕ)
    (a b k : ∀ i, Fin 2 × Fin (m i)) :
    (integralCoeff ρ β m a b k).natDegree ≤ 2 * Fintype.card σ := by
  refine (natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ _i : σ, 2 := Finset.sum_le_sum fun i _ =>
      natDegree_mul_le.trans (Nat.add_le_add (natDegree_quadraticCoeff ..) (natDegree_binomialCoeff ..))
    _ = _ := by simp [Nat.mul_comm]

/-- Reduction of two integral basis monomials in any algebra satisfying the axis relations. -/
theorem integral_normal_form {σ : Type*} [Fintype σ] [DecidableEq σ] (φ : R[X] →+* A) (ρ β : σ → R)
    (m : σ → ℕ) (u y : σ → A) (hu : ∀ i, u i ^ 2 = -u i - φ (C (ρ i) * X))
    (hy : ∀ i, y i ^ m i = φ (binomial (β i))) (a b : ∀ i, Fin 2 × Fin (m i)) :
    ∑ k : ∀ i, Fin 2 × Fin (m i), φ (integralCoeff ρ β m a b k) *
      (∏ i, u i ^ (k i).1.val * y i ^ (k i).2.val) =
      (∏ i, u i ^ (a i).1.val * y i ^ (a i).2.val) *
        ∏ i, u i ^ (b i).1.val * y i ^ (b i).2.val := by
  let f (i : σ) (k : Fin 2 × Fin (m i)) :=
    φ (quadraticCoeff (ρ i) (a i).1 (b i).1 k.1 * binomialCoeff (β i) (a i).2 (b i).2 k.2) *
      (u i ^ k.1.val * y i ^ k.2.val)
  simp only [integralCoeff, map_prod, ← Finset.prod_mul_distrib]
  change (∑ k : (i : σ) → Fin 2 × Fin (m i), ∏ i, f i (k i)) = _
  rw [← Fintype.prod_sum f]
  apply Finset.prod_congr rfl
  intro i _
  simp only [f, Fintype.sum_prod_type, map_mul]
  conv_lhs =>
    arg 2; ext v; arg 2; ext w
    rw [mul_mul_mul_comm]
  simp_rw [← Finset.mul_sum, binomial_normal_form φ _ _ (hy i), ← Finset.sum_mul,
    quadratic_normal_form φ _ _ (hu i)]
  ring

/-- Integral descent at length `H = 2r + 2d`, for all the quadratic/binomial structure constants. -/
theorem recover_integral_multiply {σ : Type*} [Fintype σ] [DecidableEq σ] (r : ℕ) (hr : 0 < r)
    (ρ β : σ → R) (m : σ → ℕ) (x y : (∀ i, Fin 2 × Fin (m i)) → Jet R r) (k) :
    let H := 2*r + 2*Fintype.card σ
    let input := specialize (0 : R) H ∘ liftJet 1 r
    readAtOne H r (multiply (fun a b c => specialize 0 H (integralCoeff ρ β m a b c))
        (input ∘ x) (input ∘ y) k) =
      multiply (fun a b c => specialize 1 r (integralCoeff ρ β m a b c)) x y k :=
  recover_multiply r _ hr _ (natDegree_integralCoeff ρ β m) x y k

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
