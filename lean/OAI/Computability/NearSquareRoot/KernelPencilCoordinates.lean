import OAI.Computability.NearSquareRoot.KernelRepairCoordinates
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # The binary query pencil on independent rational component rows -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PencilCoordinates

open Matrix CyclotomicCode PencilSearch PencilDescent RepairCoordinates

variable {m h b a W : ℕ}

/-- Install one independent clock matrix at every shift, then enumerate the
pairs by the same numbering used for the correction table. -/
def assemble (e : Signature m × Clock h b ≃ Fin W) :
    (Signature m → Matrix (Clock h b) (Clock h b) (Number a)) →+*
      Matrix (Fin W) (Fin W) (Number a) :=
  (reindexRingEquiv (Number a) ((Equiv.prodComm _ _).trans e)).toRingHom.comp
    (blockDiagonalRingHom _ _ _)

theorem assemble_entry (e : Signature m × Clock h b ≃ Fin W)
    (M : Signature m → Matrix (Clock h b) (Clock h b) (Number a)) (i j : Fin W) :
    assemble e M i j = if (e.symm i).1 = (e.symm j).1 then
      M (e.symm i).1 (e.symm i).2 (e.symm j).2 else 0 := rfl

/-- Coefficients across the numbered rows of one constant or query term. -/
def indexedCoefficient (e : Signature m × Clock h b ≃ Fin W) (A : Coefficients a m h b)
    (q : Option (Fin m)) : Matrix (Fin W) (Fin W) (Number a) :=
  assemble e fun β => Matrix.of (A β q)

private def flattenHom (I : Type*) [Fintype I] [DecidableEq I] :
    Matrix I I (Number a) →+* Matrix (I × Coord a) (I × Coord a) ℚ where
  toFun := flattenRat
  map_zero' := flattenRat_zero
  map_one' := flattenRat_one
  map_add' := flattenRat_add
  map_mul' := flattenRat_mul

/-- At a frequency with signature `k`, each query term acts by its rational sign. -/
def rationalStage (e : Signature m × Clock h b ≃ Fin W) (A : Coefficients a m h b)
    (k : Signature m) : Matrix (Fin W × Coord a) (Fin W × Coord a) ℚ :=
  flattenRat (indexedCoefficient e A none) +
    ∑ j, ((-1 : ℚ) ^ (k j).val) • flattenRat (indexedCoefficient e A (some j))

private theorem stage_blocks (A : Coefficients a m h b) (k : Signature m) :
    (fun β => stage A k β) =
      (fun β => Matrix.of (A β none)) + ∑ j, (-1 : ℤ) ^ (k j).val •
        (fun β => Matrix.of (A β (some j))) := by
  funext β
  simp only [stage, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← Int.cast_smul_eq_zsmul (Number a)]
  simp [sign]

theorem rationalStage_eq (e : Signature m × Clock h b ≃ Fin W)
    (A : Coefficients a m h b) (k : Signature m) :
    rationalStage e A k = flattenRat (assemble e (fun β => stage A k β)) := by
  let F := (flattenHom (a := a) (Fin W)).comp (assemble e)
  change _ = F (fun β => stage A k β)
  rw [stage_blocks, map_add, map_sum]
  unfold rationalStage
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℚ]
  simp [F, flattenHom, indexedCoefficient]

private theorem assemble_diagonal (e : Signature m × Clock h b ≃ Fin W)
    (p : Signature m → Number a) :
    assemble e (fun β => p β • 1) = diagonal (fun i => p (e.symm i).1) := by
  ext i j
  rw [assemble_entry]
  by_cases hij : i = j
  · simp [hij]
  · have hn : e.symm i ≠ e.symm j := e.symm.injective.ne hij
    by_cases h₁ : (e.symm i).1 = (e.symm j).1
    · have h₂ : (e.symm i).2 ≠ (e.symm j).2 := fun hh => hn (Prod.ext h₁ hh)
      simp [hij, h₁, h₂]
    · simp [hij, h₁]

/-- After the prescribed number of stages, the spectral action on the
numbered rational rows is the matrix of their predicted multipliers. -/
theorem rationalStage_pow [NeZero b] (e : Signature m × Clock h b ≃ Fin W)
    (A : Coefficients a m h b) (hA : Good A) (k : Signature m) :
    rationalStage e A k ^ b =
      flattenRat (diagonal (fun i => prediction A k (e.symm i).1)) := by
  rw [rationalStage_eq, ← flattenRat_pow, ← map_pow]
  congr 1
  rw [← assemble_diagonal e (prediction A k)]
  congr 1
  funext β
  exact hA.1 k β

variable {V ν : Type*} [AddCommGroup V] [Module ℚ V]

/-- A rational matrix on an arbitrary family of rows, repeated at each address. -/
def mix {I J : Type*} [Fintype J] (M : Matrix I J ℚ) (v : J → V) (i : I) : V :=
  ∑ j, M i j • v j

theorem mix_spectral {I J : Type*} [Fintype J] (M : Matrix I J ℚ)
    (S : V ≃ₗ[ℚ] (ν → ℚ)) (v : J → V) (ω : ν) :
    (fun i => S (mix M v i) ω) = M *ᵥ (fun j => S (v j) ω) := by
  funext i
  simp [mix, Matrix.mulVec, dotProduct, Finset.sum_apply]

/-- The ordinary stage requires just the constant row matrix and one fixed
row matrix after each distinct query. -/
def rationalStep (e : Signature m × Clock h b ≃ Fin W) (A : Coefficients a m h b)
    (Q : Fin m → Module.End ℚ V) (v : Fin W × Coord a → V) (i : Fin W × Coord a) : V :=
  mix (flattenRat (indexedCoefficient e A none)) v i +
    ∑ j, mix (flattenRat (indexedCoefficient e A (some j))) (fun t => Q j (v t)) i

theorem rationalStep_spectral (e : Signature m × Clock h b ≃ Fin W) (A : Coefficients a m h b)
    (S : V ≃ₗ[ℚ] (ν → ℚ)) (sig : ν → Signature m) (Q : Fin m → Module.End ℚ V)
    (hQ : ∀ j v ω, S (Q j v) ω = (-1 : ℚ) ^ (sig ω j).val * S v ω)
    (v : Fin W × Coord a → V) (ω : ν) :
    (fun i => S (rationalStep e A Q v i) ω) = rationalStage e A (sig ω) *ᵥ (fun i => S (v i) ω) := by
  funext i
  simp only [rationalStage, Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec]
  simp [rationalStep, mix, Finset.sum_apply, Matrix.mulVec, dotProduct, hQ, Finset.mul_sum,
    mul_left_comm]

/-- An implementation giving the same stage spectrum has the same rational
predictor on arbitrary independent inputs after the full clock power. -/
theorem predictor_spectral [NeZero b] (e : Signature m × Clock h b ≃ Fin W)
    (A : Coefficients a m h b) (hA : Good A) (S : V ≃ₗ[ℚ] (ν → ℚ)) (sig : ν → Signature m)
    (P : (Fin W × Coord a → V) → Fin W × Coord a → V)
    (hP : ∀ v ω, (fun i => S (P v i) ω) = rationalStage e A (sig ω) *ᵥ (fun i => S (v i) ω))
    (x : Fin W × Coord a → V) (ω : ν) :
    (fun i => S (P^[b] x i) ω) =
      flattenRat (diagonal (fun i => prediction A (sig ω) (e.symm i).1)) *ᵥ
        (fun i => S (x i) ω) := by
  have hpow (n : ℕ) : (fun i => S (P^[n] x i) ω) =
      rationalStage e A (sig ω) ^ n *ᵥ (fun i => S (x i) ω) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', hP, ih, Matrix.mulVec_mulVec, pow_succ']
  simpa only [rationalStage_pow e A hA] using hpow b

end PencilCoordinates

end NearSquareRoot
end Computability
end OAI
