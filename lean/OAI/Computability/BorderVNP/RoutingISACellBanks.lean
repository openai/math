import OAI.Computability.BorderVNP.RoutingISATableState
import OAI.Computability.BorderVNP.RoutingISATableSetup

/-! # Assigning physical receiving banks to the chosen cell owners

The label digit in the declared coordinate selects the greedy group owner.
The native loop writes both this team number and the address of the cell's
fixed-stride scratch bank to the two-word table in frame position 72.
Only the addresses of the banks are constructed. Unused space in the
reserved stride is never traversed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellBanks

open VPVNP.BurstRAM

/-- Layout of cell labels, team assignments and destination bank directory. -/
structure Layout where
  /-- Primary scratch frame. -/
  frame : ℕ
  /-- Number of final cells. -/
  cells : ℕ
  /-- Coordinate alphabet size. -/
  groups : ℕ
  /-- Base of the cell label codes. -/
  labels : ℕ
  /-- Base of the greedy owner word for each group. -/
  owners : ℕ
  /-- Output table of pairs of words. -/
  dest : ℕ
  /-- Base of the receiving bank arena. -/
  bankStart : ℕ
  /-- Fixed address stride between two consecutive cell banks. -/
  stride : ℕ
  /-- Base of the powers of the coordinate alphabet. -/
  powers : ℕ
  /-- Cube control block holding the chosen coordinate. -/
  header : ℕ
  /-- Shared address controls for the cell bank and task directories. -/
  controls : ℕ
  /-- Publicly declared coordinate index. -/
  axis : ℕ
  /-- The positional factor used to decode this coordinate. -/
  place : ℕ

/-- The actual values and pointers read from the previously constructed memory. -/
def Layout.Fields (l : Layout) (mem : ℕ → ℕ) : Prop :=
  mem (l.frame+11)=l.cells ∧ mem (l.frame+74)=l.groups ∧ mem (l.frame+48)=l.labels ∧
  mem (l.frame+77)=l.owners ∧ mem (l.frame+72)=l.dest ∧ mem (l.frame+62)=l.powers ∧
  mem (l.frame+63)=l.header ∧ mem (l.frame+92)=l.controls ∧ mem (l.header+5)=l.axis ∧
  mem (l.powers+l.axis)=l.place ∧ mem (l.controls+9)=l.bankStart ∧ mem (l.controls+10)=l.stride

/-- Numeric bounds ensure every addressed word and every intermediate product fits. -/
structure Layout.Fits (l : Layout) (w : ℕ) : Prop where
  /-- Nonempty group alphabet. -/
  positive : 0 < l.groups
  /-- Nonzero place value. -/
  divisor : 0 < l.place
  /-- All fixed frame offsets and immediate constants fit. -/
  frameRoom : l.frame+93 < 2^w
  /-- The declared coordinate word is accessible. -/
  headerRoom : l.header+5 < 2^w
  /-- Its precomputed positional divisor is accessible. -/
  powerRoom : l.powers+l.axis < 2^w
  /-- Both bank controls are accessible. -/
  controlRoom : l.controls+10 < 2^w
  /-- All labels are accessible. -/
  labelRoom : l.labels+l.cells ≤ 2^w
  /-- All group owners are accessible. -/
  ownerRoom : l.owners+l.groups ≤ 2^w
  /-- The table has two words per cell and its end counter fits. -/
  tableRoom : l.dest+2*l.cells < 2^w
  /-- The entire physical cell-bank allocation fits. -/
  bankRoom : l.bankStart+l.cells*l.stride < 2^w
  /-- Writes cannot affect labels still to be processed. -/
  labelsOff : l.labels+l.cells ≤ l.dest ∨ l.dest+2*l.cells ≤ l.labels
  /-- Writes cannot affect the owner lookups. -/
  ownersOff : l.owners+l.groups ≤ l.dest ∨ l.dest+2*l.cells ≤ l.owners

/-- The group owning one cell, read as a base-alphabet digit of its actual label. -/
def Layout.group (l : Layout) (mem : ℕ → ℕ) (c : ℕ) : ℕ := (mem (l.labels+c)/l.place)%l.groups

/-- The owner's team word for one cell. -/
def Layout.owner (l : Layout) (mem : ℕ → ℕ) (c : ℕ) : ℕ := mem (l.owners+l.group mem c)

/-- Address of this cell's first supplied input word. -/
def Layout.bank (l : Layout) (c : ℕ) : ℕ := l.bankStart+c*l.stride

/-- Load all static and dynamically produced words before any directory writes. -/
def setup : Code := .block [
  .constant 0 0,.constant 1 1,.constant 2 2,
  readFrame 3 62 63 11,readFrame 4 62 63 74,readFrame 5 62 63 48,
  readFrame 6 62 63 77,readFrame 7 62 63 72,readFrame 17 62 63 92,
  .constant 18 9,.binary .add 17 17 18,.load 8 17,
  .binary .add 17 17 1,.load 9 17,
  readFrame 17 62 63 63,.constant 18 5,.binary .add 17 17 18,.load 18 17,
  readFrame 17 62 63 62,.binary .add 17 17 18,.load 10 17,
  requireLt 0 4,requireLt 0 10,.copy 11 0]

/-- Compute one group digit, fetch its true owner, and emit the two destination
words before advancing the cell cursor. -/
def step : Code := .block [
  .binary .add 13 5 11,.load 12 13,.binary .div 12 12 10,.binary .mod 12 12 4,
  .binary .add 13 6 12,.load 14 13,.binary .mul 15 11 2,.binary .add 15 7 15,
  .store 15 14,.binary .add 15 15 1,.binary .mul 16 11 9,.binary .add 16 8 16,
  .store 15 16,.binary .add 11 11 1]

/-- Complete native construction of the two-word cell receiving directory. -/
def install : Code := .seq setup (.whileLt 11 3 step)

/-- Exact output memory on the completed prefix, including all outside words. -/
def Layout.written (l : Layout) (orig : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => orig
  | i+1 => Function.update (Function.update (l.written orig i) (l.dest+2*i) (l.owner orig i))
      (l.dest+2*i+1) (l.bank i)

/-- Reads outside the output prefix still see the original word. -/
theorem Layout.written_outside (l : Layout) (orig : ℕ → ℕ) (i a : ℕ)
    (off : a < l.dest ∨ l.dest+2*i ≤ a) : l.written orig i a = orig a := by
  induction i with
  | zero => rfl
  | succ j ih =>
    rw [written, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact ih (by omega)

/-- Both physical words of every processed cell have the prescribed values. -/
theorem Layout.written_at (l : Layout) (orig : ℕ → ℕ) {i c : ℕ} (h : c < i) :
    l.written orig i (l.dest+2*c) = l.owner orig c ∧
      l.written orig i (l.dest+2*c+1) = l.bank c := by
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases he : c=i
    · subst c
      simp only [written, Function.update_self, Function.update_of_ne (by omega : l.dest+2*i ≠ l.dest+2*i+1)]
      exact ⟨trivial,trivial⟩
    · have hi : c < i := by omega
      simpa only [written, Function.update_of_ne (by omega : l.dest+2*c ≠ l.dest+2*i+1),
        Function.update_of_ne (by omega : l.dest+2*c ≠ l.dest+2*i),
        Function.update_of_ne (by omega : l.dest+2*c+1 ≠ l.dest+2*i+1),
        Function.update_of_ne (by omega : l.dest+2*c+1 ≠ l.dest+2*i)] using ih hi

/-- Registers retained throughout the counted scan. -/
def Layout.Ready (l : Layout) (z : NatState) (i : ℕ) : Prop :=
  z.reg 0=0 ∧ z.reg 1=1 ∧ z.reg 2=2 ∧ z.reg 3=l.cells ∧ z.reg 4=l.groups ∧
  z.reg 5=l.labels ∧ z.reg 6=l.owners ∧ z.reg 7=l.dest ∧ z.reg 8=l.bankStart ∧
  z.reg 9=l.stride ∧ z.reg 10=l.place ∧ z.reg 11=i

end RoutingISA.CellBanks

end BorderVNP
end Computability
end OAI
