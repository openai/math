import OAI.LinearAlgebra.FiniteFourier.OccupiedWord
import OAI.LinearAlgebra.FiniteFourier.FiberGrouping
import OAI.LinearAlgebra.FiniteFourier.FewFibers
import Mathlib.Data.Nat.Log

/-! # The occupied-fibers synchronization lemma

A constant-factor workspace overhead for each individual axis suffices for
the entire tensor product, with a depth multiplier depending only on that
overhead. Discarding spare registers is unnecessary because the algorithm
restores their arbitrarily prescribed values.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix
open scoped BigOperators

/-- The depth multiplier for capacity ratio `c`. Each group has at most
`2*k-1` axes for `k=1+⌈log₂ c⌉`, and takes at most `2*c-1` rounds per axis. -/
def fiberDepthFactor (c : ℕ) : ℕ := (2 * (Nat.clog 2 c + 1) - 1) * (2 * c - 1)

variable {K : Type*} [CommSemiring K] {ι : Type} [Fintype ι] [DecidableEq ι] {P W : ι → Type}
  [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
  [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)]

/-- Lemma `up:fibers` with an explicit constant: each input word restores its
workspace, and the tensor word restores a workspace of at most `(c-1)*B`
registers for data volume `B`. Its number of slot pairs is `fiberDepthFactor c * d`. -/
theorem occupiedWord_gridTensor {c d : ℕ} {A : ∀ i, Matrix (P i) (P i) K} (hc : 0 < c)
    (ha : ∀ i, 2 ≤ Fintype.card (P i))
    (hw : ∀ i, Fintype.card (W i) ≤ Fintype.card (P i) * (c - 1))
    (h : ∀ i, OccupiedWord (W i) d (A i)) :
    OccupiedWord (Fin (Fintype.card (∀ i, P i) * (c-1))) (fiberDepthFactor c * d) (gridTensor A) := by
  let k := Nat.clog 2 c + 1
  have hk : 0 < k := Nat.succ_pos _
  by_cases hr : k ≤ Fintype.card ι
  · have hck : c ≤ 2 ^ (k-1) := by simpa [k] using Nat.le_pow_clog (by decide : 1 < 2) c
    simpa only [fiberDepthFactor, k, Nat.mul_assoc] using
      (layerWord_grid_many hk hr hc hck ha hw h).occupied
        (W := Fin (Fintype.card (∀ i, P i) * (c-1)))
  · have hV' := layerWord_grid_few (V := Fin (Fintype.card (∀ i, P i) * (c-1)))
        hw (by simp) h
    apply LayerWord.pad (hA := hV')
    apply Nat.mul_le_mul_right
    change Fintype.card ι ≤ (2 * k - 1) * (2 * c - 1)
    calc
      Fintype.card ι ≤ 2*k-1 := by omega
      _ ≤ (2*k-1) * (2*c-1) := Nat.le_mul_of_pos_right _ (by omega)

/-- Capacity can equivalently be stated as a bound on the total number of registers of each word. -/
theorem occupiedWord_gridTensor_of_totalRegisters {c d : ℕ} {A : ∀ i, Matrix (P i) (P i) K}
    (hc : 0 < c) (ha : ∀ i, 2 ≤ Fintype.card (P i))
    (hw : ∀ i, Fintype.card (P i ⊕ W i) ≤ c * Fintype.card (P i))
    (h : ∀ i, OccupiedWord (W i) d (A i)) :
    OccupiedWord (Fin (Fintype.card (∀ i, P i) * (c-1))) (fiberDepthFactor c * d) (gridTensor A) := by
  apply occupiedWord_gridTensor hc ha _ h
  intro i
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc.ne'
  simpa [Nat.succ_mul, Nat.mul_comm, Nat.add_comm (Fintype.card (P i))] using hw i

end FiniteFourier
end LinearAlgebra
end OAI
