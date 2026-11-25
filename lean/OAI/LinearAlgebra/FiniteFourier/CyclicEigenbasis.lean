import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! # Fourier projectors for a cyclic automorphism over a ring

Unit differences of the powers of the root give character orthogonality even
over rings with zero divisors. The normalized sums project onto the individual
eigenspaces and sum to the identity.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Finset
open scoped BigOperators

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private theorem cyclicRoot_pow {m : ℕ} (u : Rˣ) (hu : u ^ m = 1) (j : ℕ) :
    (u ^ j) ^ m = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, hu, one_pow]

/-- Orthogonality of two powers of a root with unit eigenvalue differences. -/
theorem cyclicCharacter_orthogonal {m : ℕ} (u : Rˣ) (hu : u ^ m = 1)
    (hsep : ∀ i j : Fin m, i ≠ j → IsUnit ((u : R)^i.val - (u : R)^j.val))
    (i j : Fin m) :
    (∑ t : Fin m, (↑((u ^ i.val)⁻¹) : R)^t.val * (↑(u ^ j.val) : R)^t.val) =
      if i = j then (m : R) else 0 := by
  simp_rw [← mul_pow, ← Units.val_mul]
  rw [Fin.sum_univ_eq_sum_range]
  by_cases hij : i = j
  · subst j
    simp
  · rw [ite_eq_right hij]
    let v := (u^i.val)⁻¹ * u^j.val
    have hv : v ^ m = 1 := by
      simp only [v, mul_pow, inv_pow, cyclicRoot_pow u hu, inv_one, one_mul]
    have hd : IsUnit ((v : R) - 1) := by
      have he : (v : R) - 1 = (↑((u^i.val)⁻¹) : R) * ((u : R)^j.val - (u : R)^i.val) := by
        rw [mul_sub]
        simp only [v, Units.val_mul, ← Units.val_pow_eq_pow_val, Units.inv_mul]
      rw [he]
      exact ((u^i.val)⁻¹).isUnit.mul (hsep j i (Ne.symm hij))
    apply hd.mul_right_cancel
    rw [zero_mul, geom_sum_mul, ← Units.val_pow_eq_pow_val, hv, Units.val_one, sub_self]

/-- The unnormalized Fourier operator with frequency `j` of a cyclic action. -/
def cyclicSpectralSum (σ : Module.End R M) (u : Rˣ) (m j : ℕ) : Module.End R M :=
  ∑ t : Fin m, (↑((u ^ j)⁻¹) : R)^t.val • σ^t.val

/-- Fourier projection after dividing by the order of the cycle. -/
noncomputable def cyclicProjector (σ : Module.End R M) (u : Rˣ) {m : ℕ} (hm : IsUnit (m:R))
    (j : Fin m) : Module.End R M :=
  (↑(hm.unit⁻¹) : R) • cyclicSpectralSum σ u m j.val

/-- The Fourier operator takes values in the corresponding eigenspace. -/
theorem cyclicSpectralSum_eigen {m j : ℕ} (σ : Module.End R M) (u : Rˣ)
    (hσ : σ^m = 1) (hu : u^m = 1) :
    σ * cyclicSpectralSum σ u m j = (u : R)^j • cyclicSpectralSum σ u m j := by
  let a := u ^ j
  let v : Module.End R M := (↑(a⁻¹) : R) • σ
  have hv : v^m = 1 := by
    rw [smul_pow, ← Units.val_pow_eq_pow_val, inv_pow, cyclicRoot_pow u hu, inv_one,
      hσ, Units.val_one, one_smul]
  have hs : cyclicSpectralSum σ u m j = ∑ t ∈ range m, v^t := by
    simp only [cyclicSpectralSum, v, smul_pow, a]
    exact Fin.sum_univ_eq_sum_range (fun t : ℕ => (↑((u^j)⁻¹) : R)^t • σ^t) m
  have he := mul_geom_sum v m
  rw [hv, sub_self, sub_mul, one_mul, sub_eq_zero, ← hs] at he
  have h := congrArg (fun A : Module.End R M => (a : R) • A) he
  simp only [v, smul_mul_assoc, smul_smul, Units.mul_inv, one_smul] at h
  exact h

private theorem end_pow_on_eigen (σ : Module.End R M) (v : R) (x : M) (hx : σ x = v • x)
    (t : ℕ) : (σ^t) x = v^t • x := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]

/-- Projecting an eigenvector gives the vector at its own frequency and zero
at each other frequency. -/
theorem cyclicProjector_apply_eigen {m : ℕ} (σ : Module.End R M) (u : Rˣ) (hu : u^m = 1)
    (hm : IsUnit (m:R)) (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val))
    (i j : Fin m) (x : M) (hx : σ x = (u:R)^j.val • x) :
    cyclicProjector σ u hm i x = if i = j then x else 0 := by
  simp only [cyclicProjector, cyclicSpectralSum, LinearMap.smul_apply, LinearMap.sum_apply,
    end_pow_on_eigen σ _ x hx, smul_smul, ← Finset.sum_smul]
  rw [← Units.val_pow_eq_pow_val u j.val, cyclicCharacter_orthogonal u hu hs]
  by_cases hij : i = j
  · have hunit : (↑hm.unit⁻¹ : R) * m = 1 := hm.unit.inv_mul
    simp only [hij, ite_true, hunit, one_smul]
  · simp [hij]

/-- Summing over all Fourier frequencies reconstructs the original vector. -/
theorem sum_cyclicProjector {m : ℕ} (σ : Module.End R M) (u : Rˣ) (hmpos : 0 < m)
    (hu : u^m = 1) (hm : IsUnit (m:R))
    (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val)) :
    ∑ j : Fin m, cyclicProjector σ u hm j = 1 := by
  let z : Fin m := ⟨0, hmpos⟩
  have hswap (j t : ℕ) : (↑((u^j)⁻¹) : R)^t = (↑((u^t)⁻¹) : R)^j := by
    simp only [← Units.val_pow_eq_pow_val, ← inv_pow, ← pow_mul, Nat.mul_comm j t]
  have hsum (t : Fin m) :
      ∑ j : Fin m, (↑((u^j.val)⁻¹) : R)^t.val = if t = z then (m:R) else 0 := by
    simpa only [z, pow_zero, Units.val_one, one_pow, mul_one, hswap t.val] using
      cyclicCharacter_orthogonal u hu hs t z
  have hunit : (↑hm.unit⁻¹ : R) * m = 1 := hm.unit.inv_mul
  simp only [cyclicProjector, cyclicSpectralSum, ← Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hsum, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, z, pow_zero, smul_smul, hunit, one_smul]

/-- The image of each normalized projector is its full eigenspace. -/
theorem range_cyclicProjector {m : ℕ} (σ : Module.End R M) (u : Rˣ) (hm : IsUnit (m:R))
    (hu : u^m = 1) (hσ : σ^m = 1)
    (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val)) (j : Fin m) :
    (cyclicProjector σ u hm j).range = σ.eigenspace ((u:R)^j.val) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    have he := LinearMap.congr_fun (cyclicSpectralSum_eigen (j := j.val) σ u hσ hu) y
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at he
    simp only [cyclicProjector, LinearMap.smul_apply, map_smul, he, smul_comm (↑hm.unit⁻¹ : R)]
  · intro hx
    refine ⟨x, ?_⟩
    simpa using cyclicProjector_apply_eigen σ u hu hm hs j j x (Module.End.mem_eigenspace_iff.mp hx)

/-- The normalized projectors are pairwise orthogonal idempotents. -/
theorem cyclicProjector_mul {m : ℕ} (σ : Module.End R M) (u : Rˣ) (hm : IsUnit (m:R))
    (hu : u^m = 1) (hσ : σ^m = 1)
    (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val)) (i j : Fin m) :
    cyclicProjector σ u hm i * cyclicProjector σ u hm j =
      if i = j then cyclicProjector σ u hm j else 0 := by
  ext x
  have hx : (cyclicProjector σ u hm j) x ∈ σ.eigenspace ((u:R)^j.val) := by
    rw [← range_cyclicProjector σ u hm hu hσ hs j]
    exact LinearMap.mem_range_self _ _
  have he := cyclicProjector_apply_eigen σ u hu hm hs i j _ (Module.End.mem_eigenspace_iff.mp hx)
  by_cases hij : i = j <;> simpa [Module.End.mul_apply, hij] using he

end FiniteFourier
end LinearAlgebra
end OAI
