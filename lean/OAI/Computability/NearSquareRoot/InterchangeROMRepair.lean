import OAI.Computability.NearSquareRoot.InterchangeSwapSpectrum
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi

/-! # Checking a finite interchange repair table

All coefficients live in the ground ring. One matrix identity per sign pattern
checks the pencil, both check-row mixers, and the four blocks of the spectral
correction. Each matrix entry is the response to a single input basis column.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair

open Matrix NearSquareRoot.SwapSpectrum

structure Spec (R I J : Type) (m : ℕ) where
  base : Matrix I I R
  term : Fin m → Matrix I I R
  extract : Matrix J I R
  restore : Matrix I J R
  correct : (Fin m → Bool) → Bool → Bool → Matrix J J R

def charSign {R : Type} [Ring R] (b : Bool) : R := if b then -1 else 1

def signProduct {R : Type} [CommRing R] {m : ℕ} (η : Fin m → Bool) : R :=
  ∏ j, charSign (η j)

variable {R I J : Type} {m : ℕ} [CommRing R]
variable [Fintype I] [DecidableEq I] [Fintype J]

def onSign (t : Spec R I J m) (η : Fin m → Bool) : Matrix I I R :=
  t.base + ∑ j, (charSign (η j) : R) • t.term j

def response (t : Spec R I J m) (η : Fin m → Bool) (order : ℕ) (half : R) : Matrix I I R :=
  let P := (onSign t η)^order
  let H := t.extract
  let G := t.restore
  let A := t.correct η false false * (H*P) + t.correct η false true * H
  let B := t.correct η true false * (H*P) + t.correct η true true * H
  P - half • (P*(P*P)-P) - P*(G*A) + G*B

/-- The actual Boolean checker used for finite table search. -/
def accepts [DecidableEq R] (t : Spec R I J m) (order : ℕ) (half : R) : Bool :=
  @decide (∀ (η : Fin m → Bool) (i j : I), response t η order half i j =
    signProduct η * (1 : Matrix I I R) i j) (by
      refine @Fintype.decidableForallFintype _ _ (fun η => ?_) inferInstance
      refine @Fintype.decidableForallFintype _ _ (fun i => ?_) inferInstance
      refine @Fintype.decidableForallFintype _ _ (fun j => ?_) inferInstance
      infer_instance)

@[simp] theorem accepts_iff [DecidableEq R] (t : Spec R I J m) (order : ℕ) (half : R) :
    accepts t order half = true ↔ ∀ η, response t η order half = (signProduct η : R) • (1 : Matrix I I R) := by
  simp only [accepts, decide_eq_true_eq]
  constructor
  · intro h η
    ext i j
    exact h η i j
  · intro h η i j
    exact congrFun (congrFun (h η) i) j

def runSign (t : Spec R I J m) (η : Fin m → Bool) (order : ℕ) (half : R) (x : I → R) : I → R :=
  let P := (onSign t η)^order
  let px := P *ᵥ x
  let a := t.extract *ᵥ px
  let b := t.extract *ᵥ x
  let h := t.correct η false false *ᵥ a + t.correct η false true *ᵥ b
  let k := t.correct η true false *ᵥ a + t.correct η true true *ᵥ b
  px - half • (P *ᵥ (P *ᵥ px) - px) - P *ᵥ (t.restore *ᵥ h) + t.restore *ᵥ k

theorem response_mulVec (t : Spec R I J m) (η : Fin m → Bool) (order : ℕ) (half : R) (x : I → R) :
    response t η order half *ᵥ x = runSign t η order half x := by
  simp only [response, runSign, add_mulVec, sub_mulVec, smul_mulVec, ← mulVec_mulVec]

/-- The entry tests are necessary and sufficient for every simultaneous input row. -/
theorem accepts_iff_rows [DecidableEq R] (t : Spec R I J m) (order : ℕ) (half : R) :
    accepts t order half = true ↔ ∀ η x, runSign t η order half x = (signProduct η : R) • x := by
  rw [accepts_iff]
  constructor
  · intro h η x
    rw [← response_mulVec,h,smul_mulVec,one_mulVec]
  · intro h η
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [response_mulVec,h,smul_mulVec,one_mulVec]

end InterchangeROMRepair

end NearSquareRoot
end Computability
end OAI
