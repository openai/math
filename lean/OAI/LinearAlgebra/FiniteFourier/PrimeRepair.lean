import OAI.LinearAlgebra.FiniteFourier.PrimeRepairVandermonde
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Full-rate Hermite repair of a spectral prediction

All computations are at a common frequency. The repair table takes
the two syndromes `H (P X)` and `H X` and returns `a` and `z • a`.
The same pointwise pair of transposed check matrices applies to those outputs.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix Polynomial
noncomputable section

variable {R : Type*} [CommRing R]

/-- The Hermite filter `y - u (y^(ℓ+1) - y)` with `u = 1/ℓ`. -/
def hermiteFilter (ℓ : ℕ) (u : R) : R[X] := X - C u * (X ^ (ℓ+1) - X)

/-- At every ℓ-th root of unity the Hermite filter agrees with the constant
`z` modulo the square of `X - z`. This also holds in positive characteristic
and over rings with zero divisors. -/
theorem hermiteFilter_factor (ℓ : ℕ) {u z : R} (hu : u * (ℓ : R) = 1) (hz : z ^ ℓ = 1) :
    ∃ D : R[X], hermiteFilter ℓ u - C z = (X - C z)^2 * D := by
  let p := hermiteFilter ℓ u - C z
  have hv : p.eval z = 0 := by simp [p, hermiteFilter, pow_succ, hz]
  have hd : p.derivative.eval z = 0 := by
    simp [p, hermiteFilter, derivative_X_pow_succ, hz, hu]
  obtain ⟨Q, hQ⟩ := (dvd_iff_isRoot.mpr hv : X - C z ∣ p)
  have he := congrArg (fun f : R[X] => f.derivative.eval z) hQ
  have hroot : Q.eval z = 0 := by simpa [hd, derivative_mul] using he.symm
  obtain ⟨D, hD⟩ := (dvd_iff_isRoot.mpr hroot : X - C z ∣ Q)
  exact ⟨D, hQ.trans (by rw [hD]; ring)⟩

/-- The two input and output blocks of the frequency table each have `s` rows.
The inverse of the restricted checks is `L`; its transpose encodes the correction. -/
def hermiteRepairTable {j s : ℕ} (L : Matrix (Fin j) (Fin s) R) (d : Fin j → R) (z : R) :
    ((Fin s → R) × (Fin s → R)) →ₗ[R] ((Fin s → R) × (Fin s → R)) :=
  let decode := (Lᵀ.mulVecLin).comp <| (diagonal d).mulVecLin.comp <|
    L.mulVecLin.comp (LinearMap.fst R _ _ - z • LinearMap.snd R _ _)
  decode.prod (z • decode)

private theorem restrictedSyndrome {W s j : ℕ} (H : Matrix (Fin s) (Fin W) R)
    (e : Fin j ↪ Fin W) (x p : Fin W → R) (z : R) (hsupp : ∀ i ∉ Set.range e, p i = z) :
    H *ᵥ (p * x) - z • H *ᵥ x =
      (H.submatrix id e) *ᵥ (fun i => (p (e i) - z) * x (e i)) := by
  rw [← Matrix.mulVec_smul, ← Matrix.mulVec_sub]
  funext t
  symm
  refine Fintype.sum_of_injective e e.injective _ _ ?_ ?_
  · intro i hi
    change H t i * (p i * x i - z * x i) = 0
    rw [hsupp i hi, sub_self, mul_zero]
  · intro i
    change H t (e i) * ((p (e i) - z) * x (e i)) = H t (e i) * (p (e i) * x (e i) - z * x (e i))
    ring

/-- The manuscript's full-rate repair identity, with an explicit table independent
of the input. The two blocks are requested once. Evaluation of the filter uses
the first and `(ℓ+1)`-st powers of the predictor; the term `p i * Z i` uses another call. -/
theorem exists_hermiteRepairTable {W s j ℓ : ℕ} {u z : R} (hu : u * (ℓ : R) = 1)
    (hz : z ^ ℓ = 1) (p : Fin W → R) (H : Matrix (Fin s) (Fin W) R) (e : Fin j ↪ Fin W)
    (L : Matrix (Fin j) (Fin s) R) (hL : L * H.submatrix id e = 1)
    (hsupp : ∀ i ∉ Set.range e, p i = z) :
    ∃ T : ((Fin s → R) × (Fin s → R)) →ₗ[R] ((Fin s → R) × (Fin s → R)),
      ∀ (x : Fin W → R) (i : Fin W),
        let t := T (H *ᵥ (p * x), H *ᵥ x)
        let Z := Hᵀ *ᵥ t.1
        let FZ := Hᵀ *ᵥ t.2
        (p i - u * (p i ^ (ℓ + 1) - p i)) * x i - p i * Z i + FZ i = z * x i := by
  classical
  obtain ⟨D, hD⟩ := hermiteFilter_factor ℓ hu hz
  let d := fun i => D.eval (p (e i))
  refine ⟨hermiteRepairTable L d z, ?_⟩
  intro x i
  let err := fun k => (p (e k) - z) * x (e k)
  let a := Lᵀ *ᵥ diagonal d *ᵥ L *ᵥ (H *ᵥ (p * x) - z • H *ᵥ x)
  change _ - p i * (Hᵀ *ᵥ a) i + (Hᵀ *ᵥ (z • a)) i = _
  rw [Matrix.mulVec_smul]
  change _ - p i * (Hᵀ *ᵥ a) i + z * (Hᵀ *ᵥ a) i = _
  have hg (y : R) : y - u * (y ^ (ℓ + 1) - y) - z = (y-z)^2 * D.eval y := by
    simpa [hermiteFilter] using congrArg (Polynomial.eval y) hD
  by_cases hi : i ∈ Set.range e
  · obtain ⟨k,rfl⟩ := hi
    have hleft : L *ᵥ (H *ᵥ (p*x) - z • H *ᵥ x) = err := by
      rw [restrictedSyndrome H e x p z hsupp, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
    have hright : (H.submatrix id e)ᵀ * Lᵀ = 1 := by rw [← Matrix.transpose_mul, hL, Matrix.transpose_one]
    have hZ : (Hᵀ *ᵥ a) (e k) = D.eval (p (e k)) * ((p (e k) - z) * x (e k)) := by
      change ((H.submatrix id e)ᵀ *ᵥ a) k = _
      dsimp only [a]
      rw [hleft, Matrix.mulVec_mulVec, hright, Matrix.one_mulVec, Matrix.mulVec_diagonal]
    rw [hZ]
    linear_combination (x (e k)) * hg (p (e k))
  · rw [hsupp i hi, pow_succ, hz]
    ring

/-- Powers of a primitive root in the coefficient domain supply unit-difference
nodes in every specialization in which that root order was inverted at the source. -/
theorem cyclotomicRepairNodes {A : Type*} [CommRing A] [IsDomain A] {W N : ℕ} {η : A}
    (hη : IsPrimitiveRoot η N) (hN : IsUnit (N : A)) (hW : W ≤ N) (f : A →+* R) :
    Pairwise fun i j : Fin W => IsUnit ((f η) ^ i.val - (f η) ^ j.val) := by
  have hdiff {i j : Fin W} (h : j < i) : IsUnit (η ^ i.val - η ^ j.val) := by
    have hlt : j.val < i.val := h
    have hi := i.isLt
    have hunit := hη.isUnit (by omega)
    have hpow : (η ^ (i.val - j.val)) ^ N = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hη.pow_eq_one, one_pow]
    have hsub := isUnit_of_dvd_unit (sub_one_dvd_natCast_of_pow_eq_one hpow
      (hη.pow_ne_one_of_pos_of_lt (by omega) (by omega))) hN
    have hfac := (hunit.pow j.val).mul hsub
    rwa [mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le hlt.le] at hfac
  intro i j hij
  have hs : IsUnit (η ^ i.val - η ^ j.val) := by
    rcases lt_or_gt_of_ne hij with h | h
    · simpa only [neg_sub] using (hdiff h).neg
    · exact hdiff h
  simpa only [map_sub, map_pow] using hs.map f

/-- The full-rate Hermite repair tables at all frequencies, using a common matrix
of Vandermonde checks. The number of rows of each table block is the uniform
exception bound, including the case of zero exceptions. -/
theorem exists_fullRateHermiteRepair {ν : Type*} {W s ℓ : ℕ} (ρ : Fin W → R)
    (hρ : Pairwise fun i j => IsUnit (ρ i - ρ j)) {u : R} (hu : u * (ℓ : R) = 1)
    (z : ν → R) (hz : ∀ v, z v ^ ℓ = 1) (p : ν → Fin W → R)
    (J : ν → Finset (Fin W)) (hsize : ∀ v, (J v).card ≤ s)
    (hsupp : ∀ v i, i ∉ J v → p v i = z v) :
    ∃ T : ν → ((Fin s → R) × (Fin s → R)) →ₗ[R] ((Fin s → R) × (Fin s → R)),
      ∀ (v : ν) (x : Fin W → R) (i : Fin W),
        let H := repairCheck ρ s
        let t := T v (H *ᵥ (p v * x), H *ᵥ x)
        let Z := Hᵀ *ᵥ t.1
        let FZ := Hᵀ *ᵥ t.2
        (p v i - u * (p v i ^ (ℓ + 1) - p v i)) * x i - p v i * Z i + FZ i = z v * x i := by
  classical
  let equiv (v : ν) := (J v).equivFin.symm
  let e (v : ν) : Fin (J v).card ↪ Fin W :=
    (equiv v).toEmbedding.trans (Function.Embedding.subtype _)
  choose L hL using fun v => repairCheck_leftInverse ρ hρ (hsize v) (e v)
  have hbad (v : ν) (i : Fin W) (hi : i ∉ Set.range (e v)) : p v i = z v := by
    apply hsupp v i
    intro himem
    exact hi ⟨(equiv v).symm ⟨i, himem⟩, congrArg Subtype.val ((equiv v).apply_symm_apply _)⟩
  choose T hT using fun v => exists_hermiteRepairTable hu (hz v) (p v)
    (repairCheck ρ s) (e v) (L v) (hL v) (hbad v)
  exact ⟨T, hT⟩

end

end FiniteFourier
end LinearAlgebra
end OAI
