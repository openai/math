import OAI.Computability.NearSquareRoot.SynchronizedAddress
import OAI.Computability.NearSquareRoot.SynchronizedBoxLayout

/-! # Padded phase table addresses in synchronized block order

Grouping consecutive tape fields leaves the rank of a record unchanged. The
low-numbered blocks occupy the least significant positions, and the fields
inside each block have the same order as the corresponding original axes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedBlocks
open Finset

private theorem axis_lt_of_lt {d : ℕ} {b j : Fin (d/4)} (h : b < j)
    (t : Fin (count b)) (i : Fin (count j)) : axis b t < axis j i := by
  have hbj : b.val < j.val := h
  have ht := t.isLt
  have hlast := j.isLt
  change 4*b.val + t.val < 4*j.val + i.val
  unfold count at ht
  split at ht <;> omega

private theorem prefix_ite {d : ℕ} (r : Fin d → ℕ) (i : Fin d) :
    CRT.«prefix» r i = ∏ t, if t < i then r t else 1 := by
  unfold CRT.«prefix»
  simpa only [mem_Iio] using (prod_ite_mem_eq (Iio i) r).symm

/-- Splitting the preceding axes at the beginning of the current block
factors the place value into the block and local place values. -/
theorem prefix_axis {d : ℕ} (hd : 4 ≤ d) (r : Fin d → ℕ)
    (j : Fin (d/4)) (i : Fin (count j)) :
    CRT.«prefix» r (axis j i) =
      CRT.«prefix» (fun b => ∏ t, r (axis b t)) j * CRT.«prefix» (fun t => r (axis j t)) i := by
  classical
  rw [prefix_ite, ← (coordinates hd).prod_comp, Fintype.prod_sigma]
  rw [prefix_ite (fun b => ∏ t, r (axis b t)) j]
  let digit := CRT.«prefix» (fun t => r (axis j t)) i
  change (∏ b, ∏ t, if axis b t < axis j i then r (axis b t) else 1) =
    (∏ b, if b < j then ∏ t, r (axis b t) else 1) * digit
  have singled : digit = ∏ b : Fin (d/4), if j = b then digit else 1 :=
    (Fintype.prod_ite_eq j (fun _ => digit)).symm
  conv_rhs => rw [singled, ← prod_mul_distrib]
  apply prod_congr rfl
  intro b _
  rcases lt_trichotomy b j with h | rfl | h
  · rw [ite_eq_left h, ite_eq_right (ne_of_gt h), mul_one]
    exact prod_congr rfl fun t _ => ite_eq_left (axis_lt_of_lt h t i)
  · simp only [lt_irrefl, ↓reduceIte, one_mul]
    rw [show digit = ∏ t, if t < i then r (axis b t) else 1 from prefix_ite _ _]
    apply prod_congr rfl
    intro t _
    have same : axis b t < axis b i ↔ t < i := by
      change 4*b.val + t.val < 4*b.val + i.val ↔ t.val < i.val
      omega
    by_cases h : t < i <;> simp [h, same]
  · rw [ite_eq_right (not_lt.mpr h.le), ite_eq_right (ne_of_lt h), mul_one]
    apply prod_eq_one
    intro t _
    exact ite_eq_right (not_lt.mpr (axis_lt_of_lt h i t).le)

/-- The mixed-radix rank on fields agrees with first ranking each block and
then ranking the resulting tuple of blocks. -/
theorem rank_axis {d : ℕ} (hd : 4 ≤ d) (r digits : Fin d → ℕ) :
    CRT.rank r digits = CRT.rank (fun j : Fin (d/4) => ∏ i, r (axis j i))
      (fun j => CRT.rank (fun i => r (axis j i)) (fun i => digits (axis j i))) := by
  unfold CRT.rank
  rw [← (coordinates hd).sum_comp, Fintype.sum_sigma]
  apply sum_congr rfl
  intro j _
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  change CRT.«prefix» r (axis j i) * digits (axis j i) = _
  rw [prefix_axis hd, Nat.mul_assoc]

end SynchronizedBlocks

namespace BoxFin
open Finset SynchronizedBlocks

variable (box : List (ℕ × ℕ))

/-- Number of consecutive physical addresses in a block, counting the
entire padded range of every local field. -/
def blockRadix (j : Fin (box.length/4)) : ℕ := ∏ i, 2^(box.get (axis j i)).1

variable {box} {k l : ℕ} (hb : BoxShape.Valid k l box)

include hb in
theorem prod_blockRadix (hd : 4 ≤ box.length) : ∏ j, blockRadix box j = 2^k := by
  let r (i : Fin box.length) := 2^(box.get i).1
  change (∏ j, ∏ i, r (axis j i)) = _
  rw [← Fintype.prod_sigma (fun s : Σ j : Fin (box.length/4), Fin (count j) => r (axis s.1 s.2))]
  change (∏ s, r (coordinates hd s)) = _
  rw [(coordinates hd).prod_comp r]
  dsimp [r]
  rw [prod_pow_eq_pow_sum]
  exact congrArg (fun n => 2^n) ((Fin.sum_univ_fun_getElem box Prod.fst).trans hb.widthSum)

include hb in
theorem blockRadix_bounds (j : Fin (box.length/4)) :
    2 ≤ blockRadix box j ∧ blockRadix box j ≤ 2^(7*l) := by
  rw [blockRadix, prod_pow_eq_pow_sum]
  have bounds (i : Fin box.length) := hb.axisBounds _ (List.get_mem box i)
  have hu := bitWidth_le (fun i : Fin box.length => (box.get i).1) (fun i => (bounds i).2.1) j
  constructor
  · have hp := (bounds (axis j (firstAxis j))).1
    have h := single_le_sum (f := fun i : Fin (count j) => (box.get (axis j i)).1)
      (fun _ _ => Nat.zero_le _) (mem_univ (firstAxis j))
    exact (Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ _ by omega))
  · exact Nat.pow_le_pow_right (by decide) hu

variable [∀ i, NeZero (modulus box i)]

/-- Local block rank, with low-numbered axes varying fastest. -/
def blockAddressRank (j : Fin (box.length/4)) :
    BlockAddress (fun i => ZMod (modulus box i) ⊕ Fin (padding box i)) j ≃ Fin (blockRadix box j) :=
  (Equiv.piCongrRight (fun i => field hb (axis j i))).trans finPiFinEquiv

/-- Computing a physical address using block ranks gives the exact tape
index, including when any component lies in the padded tail. -/
theorem recordIndex_blockRank (hd : 4 ≤ box.length)
    (x : ResidueFourier.PaddedBox (modulus box) (padding box)) :
    (recordIndex hb x).val = CRT.rank (blockRadix box)
      (fun j => (blockAddressRank hb j (regroup hd _ x j)).val) := by
  let r (i : Fin box.length) := 2^(box.get i).1
  let digits (i : Fin box.length) := field hb i (x i)
  change (finPiFinEquiv digits).val = _
  rw [← CRT.rank_eq_finPiFinEquiv r, rank_axis hd]
  apply congrArg (CRT.rank (blockRadix box))
  funext j
  exact CRT.rank_eq_finPiFinEquiv (fun i => r (axis j i)) (fun i => digits (axis j i))

end BoxFin

end NearSquareRoot
end Computability
end OAI
