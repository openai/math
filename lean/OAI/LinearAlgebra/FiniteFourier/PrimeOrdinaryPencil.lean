import OAI.LinearAlgebra.FiniteFourier.PrimeWindowPencil

/-! # An ordinary pencil stage on the clock rows

Each coefficient matrix mixes rows inside a shift block. The nonconstant
terms apply powers of the corresponding queries to the resulting rows.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Matrix MvPolynomial Finset

variable {K V ν : Type*} [CommRing K] [AddCommGroup V] [Module K V]
variable {ℓ m b h : ℕ} [NeZero ℓ] {ζ : K}

variable (Q : Fin m → Module.End K V)
variable (A₀ : (Fin m → ZMod ℓ) → Matrix (Fin h → Fin b) (Fin h → Fin b) K)
variable (A : (Fin m → ZMod ℓ) → Fin m → ZMod ℓ → Matrix (Fin h → Fin b) (Fin h → Fin b) K)

/-- Apply one ordinary stage with constant coefficient matrices and powers of the queries. -/
def queryPencilStage (x : Fin (ℓ ^ m * b ^ h) → V) (i : Fin (ℓ ^ m * b ^ h)) : V :=
  let e := clockShiftRowEquivFin ℓ m b h
  let r := e.symm i
  let mix (B : Matrix (Fin h → Fin b) (Fin h → Fin b) K) := ∑ v, B r.2 v • x (e (r.1, v))
  mix (A₀ r.1) + ∑ j, ∑ a ∈ (univ : Finset (ZMod ℓ)).erase 0, (Q j ^ a.val) (mix (A r.1 j a))

variable (hζ : IsPrimitiveRoot ζ ℓ) (S : V ≃ₗ[K] (ν → K)) (k : ν → Fin m → ZMod ℓ)
variable (hQ : ∀ j x ω, S (Q j x) ω = digitPhase hζ (k ω j) * S x ω)

include hQ in
/-- Every power of a query acts by the corresponding Fourier phase. -/
theorem queryPower_spectral_apply (j : Fin m) (a : ZMod ℓ) (x : V) (ω : ν) :
    S ((Q j ^ a.val) x) ω = queryPowerValues hζ (k ω) (j, a) * S x ω := by
  have hp (n : ℕ) : S ((Q j ^ n) x) ω = digitPhase hζ (k ω j) ^ n * S x ω := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Module.End.mul_apply, hQ, ih, pow_succ', mul_assoc]
  rw [hp]
  congr 1
  change _ = digitPhase hζ (a * k ω j)
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]

include hQ in
/-- Under the query eigenvalue hypotheses, the ordinary stage equals the
specialized pencil on every frequency. -/
theorem queryPencilStage_eq_countPencilStep
    (L : (Fin m → ZMod ℓ) → Matrix (Fin h → Fin b) (Fin h → Fin b) (MvPolynomial (Fin m × ZMod ℓ) K))
    (hL : ∀ β u, (L β).map (eval (queryPowerValues hζ u)) =
      A₀ β + ∑ j, ∑ a ∈ (univ : Finset (ZMod ℓ)).erase 0, queryPowerValues hζ u (j, a) • A β j a) :
    queryPencilStage Q A₀ A = countPencilStep hζ S k L := by
  funext x i
  apply S.injective
  ext ω
  simp only [queryPencilStage, countPencilStep, LinearEquiv.apply_symm_apply, map_add, map_sum,
    Pi.add_apply, Finset.sum_apply, queryPower_spectral_apply Q hζ S k hQ, map_smul,
    Pi.smul_apply, smul_eq_mul, hL, add_mulVec, sum_mulVec, smul_mulVec]
  simp only [mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
