import OAI.LinearAlgebra.FiniteFourier.PrimeRepair

/-! # The full-rate Hermite repair program in ordinary coordinates -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix
noncomputable section

variable {R V ν : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A fixed scalar matrix combines rows pointwise. -/
def repairMixRows {m n : ℕ} (H : Matrix (Fin m) (Fin n) R) (x : Fin n → V) (i : Fin m) : V :=
  ∑ j, H i j • x j

private theorem spectral_repairMixRows (S : V ≃ₗ[R] (ν → R)) {m n : ℕ}
    (H : Matrix (Fin m) (Fin n) R) (x : Fin n → V) (i : Fin m) (v : ν) :
    S (repairMixRows H x i) v = (H *ᵥ fun j => S (x j) v) i := by
  simp [repairMixRows, Matrix.mulVec, dotProduct, Finset.sum_apply]

/-- One table on two blocks of `s` rows. Each block has one forward and
one inverse conversion per row. -/
def ordinaryRepairTable {s : ℕ} (S : V ≃ₗ[R] (ν → R))
    (T : ν → ((Fin s → R) × (Fin s → R)) →ₗ[R] ((Fin s → R) × (Fin s → R)))
    (v₁ v₂ : Fin s → V) : (Fin s → V) × (Fin s → V) :=
  let outputs := fun ω => T ω (fun i => S (v₁ i) ω, fun i => S (v₂ i) ω)
  (fun i => S.symm (fun ω => (outputs ω).1 i), fun i => S.symm (fun ω => (outputs ω).2 i))

/-- The instruction sequence uses one predictor application for `px`,
`ℓ` additional iterations on `px`, and one application to the correction. -/
def hermiteRepairProgram {W s : ℕ} (ℓ : ℕ) (u : R) (P : (Fin W → V) → (Fin W → V))
    (S : V ≃ₗ[R] (ν → R)) (H : Matrix (Fin s) (Fin W) R)
    (T : ν → ((Fin s → R) × (Fin s → R)) →ₗ[R] ((Fin s → R) × (Fin s → R)))
    (x : Fin W → V) : Fin W → V :=
  let px := P x
  let t := ordinaryRepairTable S T (repairMixRows H px) (repairMixRows H x)
  let Z := repairMixRows Hᵀ t.1
  let FZ := repairMixRows Hᵀ t.2
  fun i => px i - u • ((P^[ℓ] px) i - px i) - P Z i + FZ i

/-- One spectral table and at most `ℓ+2` uses of the predictor implement
the common multiplier on all original rows simultaneously. -/
theorem exists_correct_hermiteRepairProgram {W s ℓ : ℕ} (S : V ≃ₗ[R] (ν → R))
    (ρ : Fin W → R) (hρ : Pairwise fun i j => IsUnit (ρ i - ρ j))
    {u : R} (hu : u * (ℓ : R) = 1) (z : ν → R) (hz : ∀ ω, z ω ^ ℓ = 1)
    (p : ν → Fin W → R) (P : (Fin W → V) → (Fin W → V))
    (hP : ∀ (x : Fin W → V) (i : Fin W) (ω : ν), S (P x i) ω = p ω i * S (x i) ω)
    (J : ν → Finset (Fin W)) (hsize : ∀ ω, (J ω).card ≤ s)
    (hsupp : ∀ ω i, i ∉ J ω → p ω i = z ω) :
    ∃ T : ν → ((Fin s → R) × (Fin s → R)) →ₗ[R] ((Fin s → R) × (Fin s → R)),
      ∀ (x : Fin W → V) (i : Fin W),
        hermiteRepairProgram ℓ u P S (repairCheck ρ s) T x i = S.symm (z * S (x i)) := by
  obtain ⟨T, hT⟩ := exists_fullRateHermiteRepair ρ hρ hu z hz p J hsize hsupp
  refine ⟨T, fun x i => ?_⟩
  apply S.injective
  ext ω
  have hiter (k : ℕ) (y : Fin W → V) :
      S (P^[k] y i) ω = p ω i ^ k * S (y i) ω := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', hP, ih, pow_succ]
      ring
  have h := hT ω (fun j => S (x j) ω) i
  dsimp only [hermiteRepairProgram]
  simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    LinearEquiv.apply_symm_apply, Pi.mul_apply, hiter, hP, spectral_repairMixRows, ordinaryRepairTable]
  convert h using 1
  ring_nf
  rfl

end

end FiniteFourier
end LinearAlgebra
end OAI
