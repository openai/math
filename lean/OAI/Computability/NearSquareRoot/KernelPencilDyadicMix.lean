import OAI.Computability.NearSquareRoot.KernelPencilDescent
import OAI.Computability.NearSquareRoot.KernelPassMatrixTable

/-! # Physical row numbers and dyadic coefficients for a binary pencil

The mix instruction numbers every basis component of every extension input
and output separately. Its table has a signed integer numerator and a natural
binary fractional width at each entry. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PencilDyadicMix

open CyclotomicCode PencilDescent KernelPass Matrix
open scoped CyclotomicCode

/-- Convert canonical signed dyadics to the coefficient format of the pass language. -/
def encode : Dyadic → Coefficient
  | .zero => (0,0)
  | .ofOdd n (.ofNat k) _ => (n,k)
  | .ofOdd n (.negSucc k) _ => (n * 2^(k+1),0)

theorem value_encode (c : Dyadic) : value (encode c) = c.toRat := by
  cases c with
  | zero => simp [encode, value]
  | ofOdd n k hn =>
    cases k with
    | ofNat k => simp [encode, value, Dyadic.toRat_ofOdd_eq_mul_two_pow, div_eq_mul_inv]
    | negSucc k =>
      rw [Dyadic.toRat_ofOdd_eq_mul_two_pow, show -(Int.negSucc k) = ((k+1 : ℕ) : ℤ) from rfl,
        zpow_natCast]
      simp [encode, value]

variable {a A i o : ℕ} {I O : Type*}

/-- Finite physical row numbering, with contiguous basis components per input. -/
def rowEquiv (a : ℕ) (e : I ≃ Fin i) : I × Coord a ≃ Fin (i * 2^a) :=
  (e.prodCongr (Equiv.refl _)).trans finProdFinEquiv

/-- Signed dyadic table in the physical row numbering. For a sequence of
bank operations the enumerations may place sum-type blocks consecutively. -/
def rowTable (eo : O × Coord a ≃ Fin o) (ei : I × Coord a ≃ Fin i) (M : Matrix O I (Number a)) :
    Fin o → Fin i → Coefficient :=
  fun u v => encode (flatten M (eo.symm u) (ei.symm v))

theorem rowTable_mulVec [Fintype I] (eo : O × Coord a ≃ Fin o) (ei : I × Coord a ≃ Fin i)
    (M : Matrix O I (Number a)) (x : Fin i → ℚ) (u : O × Coord a) :
    (∑ v, value (rowTable eo ei M (eo u) v) * x v) = (flattenRat M *ᵥ (x ∘ ei)) u := by
  rw [← ei.sum_comp]
  simp only [rowTable, value_encode, Equiv.symm_apply_apply]
  rfl

/-- One physical mix instruction for a rectangular matrix of extension scalars. -/
def rowMix (A : ℕ) (eo : O ≃ Fin o) (ei : I ≃ Fin i) (M : Matrix O I (Number a)) :
    Plan A (i * 2^a) (o * 2^a) :=
  .mix (rowTable (rowEquiv a eo) (rowEquiv a ei) M)

@[simp] theorem rowMix_calls (eo : O ≃ Fin o) (ei : I ≃ Fin i) (M : Matrix O I (Number a)) :
    (rowMix A eo ei M).calls = 0 := rfl

/-- The finite row table is shared by every address width. -/
theorem eval_rowMix (h : ℕ) (eo : O ≃ Fin o) (ei : I ≃ Fin i) (M : Matrix O I (Number a))
    (u : O × Coord a) (v : I × Coord a) (y x : Addr A h) :
    ((rowMix A eo ei M).eval h) (rowEquiv a eo u,y) (rowEquiv a ei v,x) =
      if x = y then (flatten M u v).toRat else 0 := by
  simp [rowMix, rowTable, Plan.eval, value_encode]

/-- Exact matrix action of the mixed rows on arbitrary rational input data. -/
theorem applyAt_rowMix [Fintype I] {h : ℕ} (eo : O ≃ Fin o) (ei : I ≃ Fin i)
    (M : Matrix O I (Number a)) (x : Bank A h (i * 2^a)) (u : O × Coord a) (y : Addr A h) :
    (rowMix A eo ei M).applyAt h x (rowEquiv a eo u) y =
      (flattenRat M *ᵥ (fun j => x (rowEquiv a ei j) y)) u := by
  rw [rowMix, Plan.applyAt_mix]
  exact rowTable_mulVec _ _ M (fun j => x j y) u

/-- Per-address extension matrix selected by the sum of the column signatures.
Both the check-bank enumeration and its partition are supplied by the caller. -/
theorem applyAt_matrixTable [Fintype I] {h m : ℕ} (test : Column A → Fin m → ZMod 2)
    (eo : O × Coord a ≃ Fin o) (ei : I × Coord a ≃ Fin i)
    (M : (Fin m → ZMod 2) → Matrix O I (Number a)) (x : Bank A h i)
    (u : O × Coord a) (y : Addr A h) :
    (Plan.matrixTable test (fun t => rowTable eo ei (M t))).applyAt h x (eo u) y =
      (flattenRat (M (∑ t, test (y t))) *ᵥ (fun j => x (ei j) y)) u := by
  rw [Plan.applyAt_matrixTable]
  exact rowTable_mulVec _ _ _ (fun j => x j y) u

/-- The pass acts exactly as the original extension-valued matrix on every
input address, including arbitrary independent data in each dyadic lane. -/
theorem rowMix_mulVec [Fintype I] (h : ℕ) (eo : O ≃ Fin o) (ei : I ≃ Fin i)
    (M : Matrix O I (Number a)) (x : Addr A h → I × Coord a → Dyadic)
    (u : O × Coord a) (y : Addr A h) :
    ((rowMix A eo ei M).eval h *ᵥ fun p => (x p.2 ((rowEquiv a ei).symm p.1)).toRat)
      (rowEquiv a eo u,y) = (unpack (M *ᵥ pack (x y)) u).toRat := by
  rw [← flatten_mulVec]
  change (rowMix A eo ei M).applyAt h
    (fun z t => (x t ((rowEquiv a ei).symm z)).toRat) (rowEquiv a eo u) y = _
  rw [applyAt_rowMix]
  simp only [Equiv.symm_apply_apply]
  change (∑ j : I × Coord a, toRatHom (flatten M u j) * toRatHom (x y j)) =
    toRatHom (∑ j : I × Coord a, flatten M u j * x y j)
  rw [map_sum]
  simp only [map_mul]

end PencilDyadicMix

end NearSquareRoot
end Computability
end OAI
