import OAI.Computability.VPVNP.SlotGraph
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

namespace OAI
/-! # The cyclic lane cursor of the diagonal RAM trace

Adding a coordinate in `Fin 2` is bitwise XOR. The displacement traversed
after `t` stages consists of the offset bits strictly below `t`. This
description specifies every intermediate lane and the slot that joins it
to the next one in the compressor's regular lifted graph.
-/

namespace ThreeFlat.Diagonal.LaneCursor

abbrev Lane (k : ℕ) := Fin k → Fin 2

/-- The high row bits identify the contiguous bucket of width `2^low`. -/
def highBits (k low row : ℕ) : Lane k := fun i =>
  if (row >>> low).testBit i.val then 1 else 0

theorem highBits_xor (k low row offset : ℕ) :
    highBits k low (row ^^^ offset) = highBits k low row + highBits k low offset := by
  funext i
  simp only [highBits, Pi.add_apply, Nat.testBit_shiftRight, Nat.testBit_xor]
  cases row.testBit (low + i.val) <;> cases offset.testBit (low + i.val) <;> decide

variable {k : ℕ}

/-- Lane displacement on the straight or flipping arc at coordinate `i`. -/
def axis (i : Fin k) (bit : Fin 2) : Lane k := fun j => if j = i then bit else 0

/-- The bits of the offset already traversed by the cursor. -/
def traversed (offset : Lane k) (t : ℕ) : Lane k := fun j =>
  if j.val < t then offset j else 0

@[simp] theorem traversed_zero (offset : Lane k) : traversed offset 0 = 0 := by
  funext i
  simp [traversed]

@[simp] theorem traversed_end (offset : Lane k) : traversed offset k = offset := by
  funext i
  simp [traversed, i.isLt]

theorem traversed_next (offset : Lane k) (i : Fin k) :
    traversed offset (i.val + 1) = traversed offset i.val + axis i (offset i) := by
  funext j
  by_cases eq : j = i
  · subst j
    simp [traversed, axis]
  · have hv : j.val ≠ i.val := fun h => eq (Fin.ext h)
    have hlt : j.val < i.val + 1 ↔ j.val < i.val := by omega
    simp [traversed, axis, eq, hlt]

/-- At every cursor position the map from source to current lane is a permutation. -/
def stage (offset : Lane k) (t : ℕ) : Equiv.Perm (Lane k) where
  toFun x := x + traversed offset t
  invFun y := y - traversed offset t
  left_inv _ := add_sub_cancel_right ..
  right_inv _ := sub_add_cancel ..

@[simp] theorem stage_zero (offset source : Lane k) : stage offset 0 source = source := by
  change source + traversed offset 0 = _
  simp

@[simp] theorem stage_end (offset source : Lane k) : stage offset k source = source + offset := by
  change source + traversed offset k = _
  simp

theorem stage_next (offset source : Lane k) (i : Fin k) :
    stage offset (i.val + 1) source = stage offset i.val source + axis i (offset i) := by
  change source + traversed offset (i.val + 1) = _
  rw [traversed_next, ← add_assoc]
  rfl

/-- A one-cycle walk is forced at every stage by its straight/flip decisions. -/
theorem walk_eq_stage (branch source : Lane k) (walk : Fin (k + 1) → Lane k)
    (start : walk 0 = source)
    (steps : ∀ i : Fin k, walk i.succ = walk i.castSucc + axis i (branch i))
    (t : Fin (k + 1)) : walk t = stage branch t.val source := by
  induction t using Fin.induction with
  | zero => simpa using start
  | succ i ih =>
    rw [steps, ih]
    exact (stage_next branch source i).symm

/-- Prescribing the two endpoints forces the branch bits themselves. -/
theorem branches_eq_offset (branch source offset : Lane k) (walk : Fin (k + 1) → Lane k)
    (start : walk 0 = source) (finish : walk (Fin.last k) = source + offset)
    (steps : ∀ i : Fin k, walk i.succ = walk i.castSucc + axis i (branch i)) :
    branch = offset := by
  have last := walk_eq_stage branch source walk start steps (Fin.last k)
  rw [finish, Fin.val_last, stage_end] at last
  exact add_left_cancel last.symm

private theorem rotate_ne (hk : 2 ≤ k) (i : Fin k) : finRotate k i ≠ i := by
  obtain _ | n := k
  · omega
  obtain ⟨i, hi⟩ := i
  intro eq
  by_cases before : i < n
  · rw [finRotate_of_lt before] at eq
    have h := congrArg Fin.val eq
    change i + 1 = i at h
    omega
  · have last : i = n := by omega
    subst i
    rw [finRotate_last'] at eq
    have h := congrArg Fin.val eq
    change 0 = n at h
    omega

/-- A repeated pair of parallel straight/flip arcs for each cursor step. The
degree is `r * 2`, so `r = 2^b` gives the compressor's power-of-two degree. -/
def graph (hk : 2 ≤ k) (r : ℕ) :
    Computability.VPVNP.Compression.LiftedSlots (Fin k) (r * 2) (Lane k) where
  base := {
    target := (finRotate k).prodCongr (Equiv.refl _)
    ends_ne := fun p => rotate_ne hk p.1
  }
  displacement := fun p => axis p.1 (finProdFinEquiv.symm p.2).2

/-- The chosen arc of the actual compressor graph joins successive path lanes.
The same choice works on every repeated pair of branches. -/
theorem actual_edge (hk : 2 ≤ k) {r : ℕ} (copy : Fin r) (offset source : Lane k) (i : Fin k) :
    (graph hk r).actualTarget
        ((i, finProdFinEquiv (copy, offset i)), stage offset i.val source) =
      ((finRotate k i, finProdFinEquiv (copy, offset i)), stage offset (i.val + 1) source) := by
  rw [Computability.VPVNP.Compression.LiftedSlots.actualTarget_apply]
  change ((finRotate k i, finProdFinEquiv (copy, offset i)),
    stage offset i.val source + axis i (finProdFinEquiv.symm (finProdFinEquiv (copy, offset i))).2) = _
  rw [Equiv.symm_apply_apply, stage_next]

end ThreeFlat.Diagonal.LaneCursor

end OAI
