import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace OAI
/-! # Chronological addresses of the diagonal simulation

A group first proposes the endpoints of its external pairs, scans a full
period of chunks, multiplies its scheduled cells, and clears its scratch.
-/

namespace ThreeFlat.Diagonal.TickChronology

/-- The zero code is idle; the six other codes are the program's entry points. -/
inductive Phase
  | idle | opening | closing | propose | scan | evaluate | clear
  deriving DecidableEq, Repr

def Phase.tag : Phase → ℕ
  | .idle => 0 | .opening => 1 | .closing => 2 | .propose => 3
  | .scan => 4 | .evaluate => 5 | .clear => 6

/-- Fixed physical clock parameters. The stop tick is excluded from the
group reservation, and the closing transition itself is numbered `last`. -/
structure Clock where
  beginTick : ℕ
  groups : ℕ
  groupDuration : ℕ
  chunks : ℕ
  evaluateTicks : ℕ
  last : ℕ
  begin_pos : 0 < beginTick
  chunks_pos : 0 < chunks
  room : chunks + evaluateTicks + 2 ≤ groupDuration
  fits : beginTick + groups*groupDuration ≤ last

def Clock.stop (c : Clock) := c.beginTick + c.groups*c.groupDuration
def Clock.base (c : Clock) (g : ℕ) := c.beginTick + g*c.groupDuration
def Clock.group (c : Clock) (t : ℕ) := (t-c.beginTick)/c.groupDuration
def Clock.offset (c : Clock) (t : ℕ) := (t-c.beginTick)%c.groupDuration

def Clock.within (c : Clock) (o : ℕ) : Phase :=
  if o = 0 then .propose else if o < c.chunks+1 then .scan
  else if o < c.chunks+c.evaluateTicks+1 then .evaluate
  else if o = c.groupDuration-1 then .clear else .idle

def Clock.phase (c : Clock) (t : ℕ) : Phase :=
  if t = 0 then .opening else if t = c.last then .closing
  else if t < c.beginTick then .idle else if t < c.stop then c.within (c.offset t) else .idle

theorem Clock.duration_pos (c : Clock) : 0 < c.groupDuration := by have := c.room; omega

theorem Clock.in_group (c : Clock) {g o : ℕ} (hg : g < c.groups) (ho : o < c.groupDuration) :
    c.phase (c.base g+o) = c.within o ∧ c.group (c.base g+o) = g ∧
    c.offset (c.base g+o) = o := by
  have hp := c.begin_pos
  have d := c.duration_pos
  have later : (g+1)*c.groupDuration ≤ c.groups*c.groupDuration :=
    Nat.mul_le_mul_right _ hg
  have lo : c.beginTick ≤ c.base g+o := by simp [Clock.base, Nat.add_assoc]
  have hi : c.base g+o < c.stop := by
    unfold Clock.base Clock.stop
    rw [Nat.add_mul, Nat.one_mul] at later
    omega
  have bound : c.base g+o < c.last := lt_of_lt_of_le hi c.fits
  have eqsub : c.base g+o-c.beginTick = o+c.groupDuration*g := by
    rw [Clock.base, Nat.mul_comm g c.groupDuration]; omega
  have hgrp : c.group (c.base g+o) = g := by
    simp [Clock.group, eqsub, Nat.add_mul_div_left _ _ d, Nat.div_eq_of_lt ho]
  have hoff : c.offset (c.base g+o) = o := by simp [Clock.offset, eqsub, Nat.mod_eq_of_lt ho]
  refine ⟨?_, hgrp, hoff⟩
  simp only [Clock.phase, ite_eq_right (show c.base g+o ≠ 0 by omega), ite_eq_right bound.ne,
    ite_eq_right (not_lt.mpr lo), ite_eq_left hi, hoff]

theorem Clock.opening (c : Clock) : c.phase 0 = .opening := by simp [Clock.phase]
theorem Clock.closing (c : Clock) : c.phase c.last = .closing := by
  have : 0 < c.last := lt_of_lt_of_le c.begin_pos (by have := c.fits; omega)
  simp [Clock.phase, this.ne']

theorem Clock.propose (c : Clock) {g : ℕ} (hg : g < c.groups) :
    c.phase (c.base g) = .propose := by
  simpa [Clock.within] using (c.in_group hg c.duration_pos).1

theorem Clock.scan (c : Clock) {g j : ℕ} (hg : g < c.groups) (hj : j < c.chunks) :
    c.phase (c.base g + (1+j)) = .scan := by
  have room := c.room
  rw [(c.in_group hg (show 1+j < c.groupDuration by omega)).1]
  simp [Clock.within, show 1+j < c.chunks+1 by omega]

theorem Clock.evaluate (c : Clock) {g j : ℕ} (hg : g < c.groups) (hj : j < c.evaluateTicks) :
    c.phase (c.base g + (c.chunks+1+j)) = .evaluate := by
  have room := c.room
  rw [(c.in_group hg (show c.chunks+1+j < c.groupDuration by omega)).1]
  simp [Clock.within, show ¬c.chunks+1+j < c.chunks+1 by omega, show c.chunks+1+j < c.chunks+c.evaluateTicks+1 by omega]

theorem Clock.clear (c : Clock) {g : ℕ} (hg : g < c.groups) :
    c.phase (c.base g + (c.groupDuration-1)) = .clear := by
  have room := c.room
  have hc := c.chunks_pos
  rw [(c.in_group hg (show c.groupDuration-1 < c.groupDuration by omega)).1]
  simp [Clock.within, show c.groupDuration-1 ≠ 0 by omega,
    show ¬c.groupDuration-1 < c.chunks+1 by omega,
    show ¬c.groupDuration-1 < c.chunks+c.evaluateTicks+1 by omega]

/-- During a scan the physical external chunk is the cyclic translate of the
scan offset. Its permutation supplies every chunk exactly once. -/
def Clock.scanOrder (c : Clock) (g : ℕ) : Equiv.Perm (Fin c.chunks) :=
  letI : NeZero c.chunks := ⟨c.chunks_pos.ne'⟩
  Equiv.addLeft (Fin.ofNat c.chunks (c.base g+1))

theorem Clock.scanOrder_val (c : Clock) (g : ℕ) (j : Fin c.chunks) :
    (c.scanOrder g j).val = (c.base g+(1+j.val))%c.chunks := by
  let : NeZero c.chunks := ⟨c.chunks_pos.ne'⟩
  change (Fin.ofNat c.chunks (c.base g+1)+j).val = _
  simp only [Fin.val_add, Fin.val_ofNat, Nat.mod_add_mod, Nat.add_assoc]

end ThreeFlat.Diagonal.TickChronology

end OAI
