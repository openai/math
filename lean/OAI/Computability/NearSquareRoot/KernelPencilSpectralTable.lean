import OAI.Computability.NearSquareRoot.KernelPencilDyadicMix
import OAI.Computability.NearSquareRoot.KernelPassFrequency
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # Spectral action of both compressed check banks in dyadic coordinates -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PencilDyadicMix

open CyclotomicCode PencilDescent KernelPass Matrix
open scoped CyclotomicCode

variable {A h m a s : ℕ}

/-- Keep the two check banks consecutive, including all basis components of
a check in the same bank. -/
def checkEquiv (a s : ℕ) :
    (Fin s ⊕ Fin s) × Coord a ≃ Fin (s*2^a + s*2^a) :=
  (Equiv.sumProdDistrib _ _ _).trans ((finProdFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv)

@[simp] theorem checkEquiv_left (i : Fin s) (k : Coord a) :
    checkEquiv a s (.inl i,k) = Fin.castAdd _ (finProdFinEquiv (i,k)) := rfl

@[simp] theorem checkEquiv_right (i : Fin s) (k : Coord a) :
    checkEquiv a s (.inr i,k) = Fin.natAdd _ (finProdFinEquiv (i,k)) := rfl

abbrev CheckRows (a s : ℕ) := Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) (Number a)

/-- Select a four-block correction matrix and perform the full spectral
conversions on the two check banks. -/
def spectralCheckTable (test : Column A → Fin m → ZMod 2)
    (T : (Fin m → ZMod 2) → CheckRows a s) : Plan A (s*2^a+s*2^a) (s*2^a+s*2^a) :=
  Plan.spectralTable test (fun t => rowTable (checkEquiv a s) (checkEquiv a s) (T t))

theorem calls_spectralCheckTable (test : Column A → Fin m → ZMod 2)
    (T : (Fin m → ZMod 2) → CheckRows a s) : (spectralCheckTable test T).calls = 4*(s*2^a)*A := by
  simp only [spectralCheckTable, Plan.calls_spectralTable]
  ring

private def merge (v w : Fin s × Coord a → ℚ) : (Fin s ⊕ Fin s) × Coord a → ℚ :=
  fun p => p.1.elim (fun i => v (i,p.2)) (fun j => w (j,p.2))

private theorem left_mulVec (t : CheckRows a s) (v w : Fin s × Coord a → ℚ) (p : Fin s × Coord a) :
    (flattenRat t *ᵥ merge v w) (.inl p.1,p.2) =
      (flattenRat t.toBlocks₁₁ *ᵥ v + flattenRat t.toBlocks₁₂ *ᵥ w) p := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type, merge, flattenRat, flatten,
    Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]

private theorem right_mulVec (t : CheckRows a s) (v w : Fin s × Coord a → ℚ) (p : Fin s × Coord a) :
    (flattenRat t *ᵥ merge v w) (.inr p.1,p.2) =
      (flattenRat t.toBlocks₂₁ *ᵥ v + flattenRat t.toBlocks₂₂ *ᵥ w) p := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type, merge, flattenRat, flatten,
    Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

/-- The component vector of one bank at one frequency, in coefficient order. -/
def frequencyRows (x : Bank A h (s * 2^a)) (y : Addr A h) : Fin s × Coord a → ℚ :=
  fun j => Plan.frequency x (finProdFinEquiv j) y

/-- Constant extension mixes commute with the Walsh conversion across
addresses. Both row matrices may be rectangular. -/
theorem frequencyRows_rowMix {i o : ℕ} (M : Matrix (Fin o) (Fin i) (Number a))
    (x : Bank A h (i * 2^a)) (y : Addr A h) :
    frequencyRows ((rowMix A (Equiv.refl _) (Equiv.refl _) M).applyAt h x) y =
      flattenRat M *ᵥ frequencyRows x y := by
  funext u
  change (∑ z, Plan.walshMatrix A h y z *
      (rowMix A (Equiv.refl _) (Equiv.refl _) M).applyAt h x (rowEquiv a (Equiv.refl _) u) z) =
    ∑ j, flattenRat M u j * (∑ z, Plan.walshMatrix A h y z * x (rowEquiv a (Equiv.refl _) j) z)
  simp only [applyAt_rowMix, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_left_comm]

private theorem frequency_append (x w : Bank A h (s * 2^a)) (y : Addr A h) :
    (fun p => Plan.frequency (Fin.append x w) (checkEquiv a s p) y) =
    merge (frequencyRows x y) (frequencyRows w y) := by
  funext p
  rcases p with ⟨i|j,k⟩
  · simp only [checkEquiv_left, Plan.frequency, Fin.append_left, merge, Sum.elim_inl, frequencyRows]
  · simp only [checkEquiv_right, Plan.frequency, Fin.append_right, merge, Sum.elim_inr, frequencyRows]

private theorem selected_action (test : Column A → Fin m → ZMod 2)
    (T : (Fin m → ZMod 2) → CheckRows a s) (x w : Bank A h (s * 2^a))
    (u : (Fin s ⊕ Fin s) × Coord a) (y : Addr A h) :
    Plan.frequency ((spectralCheckTable test T).applyAt h (Fin.append x w)) (checkEquiv a s u) y =
      (flattenRat (T (∑ t, test (y t))) *ᵥ merge (frequencyRows x y) (frequencyRows w y)) u := by
  rw [spectralCheckTable, Plan.frequency_spectralTable, rowTable_mulVec, ← frequency_append]
  rfl

/-- Frequency action on the first check bank in the physical concatenation. -/
theorem frequency_spectralCheck_left (test : Column A → Fin m → ZMod 2)
    (T : (Fin m → ZMod 2) → CheckRows a s) (x w : Bank A h (s * 2^a))
    (p : Fin s × Coord a) (y : Addr A h) :
    frequencyRows (Plan.leftPart ((spectralCheckTable test T).applyAt h (Fin.append x w))) y p =
      let t := T (∑ j, test (y j))
      (flattenRat t.toBlocks₁₁ *ᵥ frequencyRows x y + flattenRat t.toBlocks₁₂ *ᵥ frequencyRows w y) p :=
  (selected_action test T x w (.inl p.1,p.2) y).trans (left_mulVec _ _ _ p)

/-- Frequency action on the second check bank in the physical concatenation. -/
theorem frequency_spectralCheck_right (test : Column A → Fin m → ZMod 2)
    (T : (Fin m → ZMod 2) → CheckRows a s) (x w : Bank A h (s * 2^a))
    (p : Fin s × Coord a) (y : Addr A h) :
    frequencyRows (Plan.rightPart ((spectralCheckTable test T).applyAt h (Fin.append x w))) y p =
      let t := T (∑ j, test (y j))
      (flattenRat t.toBlocks₂₁ *ᵥ frequencyRows x y + flattenRat t.toBlocks₂₂ *ᵥ frequencyRows w y) p :=
  (selected_action test T x w (.inr p.1,p.2) y).trans (right_mulVec _ _ _ p)

end PencilDyadicMix

end NearSquareRoot
end Computability
end OAI
