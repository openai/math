import OAI.LinearAlgebra.FiniteFourier.PrimeFixedRepair

/-! # A fixed Hermite repair table indexed by query signs

The table for a binary template is indexed by the finite set of sign
patterns. Its entries are fixed before the length of a recursive axis,
the number of spectator axes, and the choice of normalized coordinates.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelRepair

open OAI.LinearAlgebra.FiniteFourier Matrix

variable {R : Type*} [CommRing R]

/-- Multiplying every spectral coordinate by the same normalization commutes
with the entire table and cancels in the inverse conversion. -/
theorem ordinaryRepairTable_rescale
    {V ν : Type*} [AddCommGroup V] [Module R V] {s : ℕ}
    (S S' : V ≃ₗ[R] (ν → R)) (a : R) (ha : ∀ x v, S' x v = a * S x v)
    (T : ν → ((Fin s → R) × (Fin s → R)) →ₗ[R] ((Fin s → R) × (Fin s → R)))
    (v₁ v₂ : Fin s → V) :
    ordinaryRepairTable S' T v₁ v₂ = ordinaryRepairTable S T v₁ v₂ := by
  have scaled (v : ν) :
      ((fun i => S' (v₁ i) v), fun i => S' (v₂ i) v) =
      a • ((fun i => S (v₁ i) v), fun i => S (v₂ i) v) := by
    ext i <;> exact ha _ _
  apply Prod.ext <;> funext i <;> apply S'.injective <;> funext v
  all_goals
    simp only [ordinaryRepairTable, LinearEquiv.apply_symm_apply]
    rw [ha, LinearEquiv.apply_symm_apply, scaled v, map_smul]
    rfl

/-- A pointwise table certificate implies correctness of the ordinary program
for every coordinate change and every labeling by the certified signatures. -/
theorem signature_table_correct {Sig : Type*} {W s ℓ : ℕ} (u : R)
    (z : Sig → R) (p : Sig → Fin W → R) (H : Matrix (Fin s) (Fin W) R)
    (T : Sig → ((Fin s → R) × (Fin s → R)) →ₗ[R] ((Fin s → R) × (Fin s → R)))
    (hT : ∀ a (x : Fin W → R) i,
      let t := T a (H *ᵥ (p a * x), H *ᵥ x)
      (p a i - u * (p a i ^ (ℓ + 1) - p a i)) * x i - p a i * (Hᵀ *ᵥ t.1) i +
        (Hᵀ *ᵥ t.2) i = z a * x i)
    {V ν : Type*} [AddCommGroup V] [Module R V] (S : V ≃ₗ[R] (ν → R))
    (sig : ν → Sig) (P : (Fin W → V) → Fin W → V)
    (hP : ∀ x i v, S (P x i) v = p (sig v) i * S (x i) v) (x : Fin W → V) (i : Fin W) :
    hermiteRepairProgram ℓ u P S H (T ∘ sig) x i = S.symm ((z ∘ sig) * S (x i)) := by
  have iter (n : ℕ) (y : Fin W → V) (ω : ν) :
      S (P^[n] y i) ω = p (sig ω) i ^ n * S (y i) ω := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', hP, ih, pow_succ]
      ring
  have mix {j t : ℕ} (H : Matrix (Fin t) (Fin j) R) (v : Fin j → V) (w : Fin t) (ω : ν) :
      S (repairMixRows H v w) ω = (H *ᵥ fun i => S (v i) ω) w := by
    simp [repairMixRows, Matrix.mulVec, dotProduct, Finset.sum_apply]
  apply S.injective
  funext ω
  have hc := hT (sig ω) (fun j => S (x j) ω) i
  dsimp only [hermiteRepairProgram]
  simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    LinearEquiv.apply_symm_apply, Pi.mul_apply, iter, hP, mix, ordinaryRepairTable, Function.comp_apply]
  convert hc using 1
  ring_nf
  rfl

/-- If the predictor and exceptional set depend only on a signature, the
resulting *one* table works on every spectral space carrying that signature.
Both inputs and both outputs have exactly `s` rows. -/
theorem exists_signature_table {Sig : Type*} {W s ℓ : ℕ}
    (nodes : Fin W → R) (hnodes : Pairwise fun i j => IsUnit (nodes i - nodes j))
    {u : R} (hu : u * (ℓ : R) = 1) (z : Sig → R) (hz : ∀ a, z a ^ ℓ = 1)
    (p : Sig → Fin W → R) (J : Sig → Finset (Fin W)) (hsize : ∀ a, (J a).card ≤ s)
    (hsupp : ∀ a i, i ∉ J a → p a i = z a) :
    ∃ T : Sig → ((Fin s → R) × (Fin s → R)) →ₗ[R] ((Fin s → R) × (Fin s → R)),
      ∀ {V ν : Type} [AddCommGroup V] [Module R V] (S : V ≃ₗ[R] (ν → R))
        (sig : ν → Sig) (P : (Fin W → V) → Fin W → V),
        (∀ x i v, S (P x i) v = p (sig v) i * S (x i) v) →
        ∀ x i, hermiteRepairProgram ℓ u P S (repairCheck nodes s) (T ∘ sig) x i =
          S.symm ((z ∘ sig) * S (x i)) := by
  obtain ⟨T, hT⟩ := exists_fullRateHermiteRepair nodes hnodes hu z hz p J hsize hsupp
  exact ⟨T, fun S sig P hP x i => signature_table_correct u z p _ T hT S sig P hP x i⟩

/-- A single finite table on the `2^m` possible sign tuples works for every
binary Fourier query family. The query count, clock order, batch size and
check count all precede the choice of row space and spectral coordinates. -/
theorem binary_repair_table {ζ : R} {m b : ℕ} {hζ : IsPrimitiveRoot ζ 2}
    [PrimeSpectrumOrthogonal hζ] (p : PrimeRepairPencil 2 m b hζ)
    (hm : 2 ≤ m) (u : R) (hu : u * 2 = 1)
    (ρ : Fin (primePredictorRows 2 m b) → R) (hρ : Pairwise fun i j => IsUnit (ρ i - ρ j)) :
    let s := countRepairChecks 2 m (b ^ primeClockDigits 2 m b)
    ∃ T : (Fin m → ZMod 2) → ((Fin s → R) × (Fin s → R)) →ₗ[R] ((Fin s → R) × (Fin s → R)),
      ∀ {V ν : Type} [AddCommGroup V] [Module R V] (S : V ≃ₗ[R] (ν → R))
        (k : ν → Fin m → ZMod 2) (Q : Fin m → Module.End R V),
        (∀ j x ω, S (Q j x) ω = digitPhase hζ (k ω j) * S x ω) →
        ∀ x i, hermiteRepairProgram 2 u (queryPencilStage Q p.A₀ p.A)^[b]
          S (repairCheck ρ s) (T ∘ k) x i =
          S.symm ((countQueryProduct hζ ∘ k) * S (x i)) := by
  let B := b ^ primeClockDigits 2 m b
  have inv : u * ((2 : ℕ) : R) = 1 := by simpa using hu
  obtain ⟨T, hT⟩ := exists_signature_table (W := primePredictorRows 2 m b) ρ hρ inv
    (countQueryProduct hζ) (countQueryProduct_pow hζ)
    (fun k => countPredictorEigenvalue (B := B) hζ k)
    (fun k => exceptionalShiftRowIndices k B)
    (fun k => exceptionalShiftRowIndices_card_le (by decide : 2 ≤ 2) hm k B)
    (by
      intro k i hi
      have hw := not_not.mp ((mem_exceptionalShiftRowIndices _ _).not.mp hi)
      exact eval_countPredictor_of_orthogonal hζ (isUnit_iff_exists_inv'.mpr ⟨u, inv⟩)
        _ _ hw.1 (by simpa only [repairWindowLower_add_degree] using hw.2))
  refine ⟨T, ?_⟩
  intro V ν _ _ S k Q hQ
  apply hT S k
  rw [queryPencilStage_eq_countPencilStep Q p.A₀ p.A hζ S k hQ p.L p.stage]
  exact countPencilStep_iterate_predictor hζ S k p.L p.power

end KernelRepair

end NearSquareRoot
end Computability
end OAI
