import OAI.Computability.BorderVNP.RoutingISATableState
import OAI.Computability.BorderVNP.RoutingISARegisterFrame
import OAI.Computability.BorderVNP.PackedBottomReportSources
import OAI.Computability.BorderVNP.CellDirectoryWire

/-! # Native writer for a bottom box's report bindings

The delivered sidecar lists three words for each weighted source. The third
word is its relative report lane. The writer binds that lane for all copies
to a consecutive interval of use guesses and pins the unused lanes to zero.
Its only stores go to the supplied output cursor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.Writer

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM CellSparse

/-- Consecutive scalar stores, advancing the packet cursor in register 28. -/
def push : List Reg → Code
  | [] => .nop
  | r :: rs => .seq (.store 28 r) (.seq (.binary .add 28 28 42) (push rs))

/-- The count and the loop's small constants. -/
def setup : Code := .block [.constant 40 0, .load 41 20, .constant 42 1,
  .constant 43 0, .constant 44 3]

/-- Read the third word of the current sidecar position and rebase its report lane. -/
def readLane : Code := .block [.binary .add 45 40 42, .binary .mul 45 45 44,
  .binary .add 45 20 45, .load 46 45, .binary .add 46 25 46]

/-- A tagged equality record, with both three-word ports in packet order. -/
def equalRegs : List Reg := [42,21,42,46,26,42,24,42,42]

/-- Advance to the next source and its block of use guesses. -/
def advance : Code := .block [.binary .add 24 24 21, .binary .add 29 29 42,
  .binary .add 40 40 42]

/-- Emit one equality for the entire bundle of copies. -/
def body : Code := .block [readLane, push equalRegs, advance]

/-- Rebase the unused suffix and measure its length. -/
def tailLane : Code := .block [.binary .sub 47 27 41, .binary .add 46 19 41,
  .binary .add 46 25 46]

/-- A tagged zero record with its three-word port. -/
def zeroRegs : List Reg := [43,21,47,46,26,42]

/-- Emit a single zero record. A zero-length suffix has a valid empty check. -/
def finish : Code := .block [tailLane,push zeroRegs,.binary .add 29 29 42]

/-- Fixed native report writer. The input pointer and all other caller registers
below 40 except the three output cursors are preserved. -/
def program : Code := .block [setup,.whileLt 40 41 body,finish]

/-- Chronological effect of consecutive scalar stores. -/
def write (m : ℕ → ℕ) (a : ℕ) : List ℕ → ℕ → ℕ
  | [] => m
  | x :: xs => write (Function.update m a x) (a+1) xs

/-- Concatenation of packet fragments is chronological composition of their stores. -/
theorem write_append (m : ℕ → ℕ) (a : ℕ) (xs ys : List ℕ) :
    write m a (xs++ys) = write (write m a xs) (a+xs.length) ys := by
  induction xs generalizing m a with
  | nil => simp [write]
  | cons x xs ih => simp only [List.cons_append,List.length_cons,write,ih]; congr 1; omega

/-- Words before and after the emitted packet survive every store. -/
theorem write_outside (m : ℕ → ℕ) (a : ℕ) (xs : List ℕ) (j : ℕ)
    (outside : j < a ∨ a+xs.length ≤ j) : write m a xs j = m j := by
  induction xs generalizing a m with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons] at outside
    rw [write, ih _ _ (by omega), Function.update_of_ne (by omega : j ≠ a)]

/-- Each output word equals the corresponding scalar in the packet. -/
theorem write_read (m : ℕ → ℕ) (a : ℕ) (xs : List ℕ) (i : Fin xs.length) :
    write m a xs (a+i) = xs[i] := by
  induction xs generalizing m a with
  | nil => exact i.elim0
  | cons x xs ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [Fin.val_zero,Nat.add_zero,write]
      rw [write_outside _ _ _ _ (Or.inl (by omega)),Function.update_self]
      rfl
    · simpa [write,Nat.add_assoc,Nat.add_comm 1] using ih (Function.update m a x) (a+1) k

private theorem push_eval (pub : Arg → ℕ) (z : NatState) (rs : List Reg)
    (unit : z.reg 42 = 1) (fresh : 28 ∉ rs) :
    (push rs).fixedEval pub z =
      ⟨Function.update z.reg 28 (z.reg 28 + rs.length), write z.mem (z.reg 28) (rs.map z.reg)⟩ := by
  induction rs generalizing z with
  | nil => simp [push,Code.fixedEval,Code.evalNat,write,Function.update_eq_self]
  | cons r rs ih =>
    let u : NatState := ⟨Function.update z.reg 28 (z.reg 28+1),
      Function.update z.mem (z.reg 28) (z.reg r)⟩
    have htail : 28 ∉ rs := fun h => fresh (.tail _ h)
    have hu : u.reg 42 = 1 := by simpa [u] using unit
    have hmap : rs.map u.reg = rs.map z.reg := by
      apply List.map_congr_left
      intro v hv
      have hne : v ≠ (28 : Reg) := by rintro rfl; exact htail hv
      exact Function.update_of_ne hne ..
    have head : (push (r::rs)).fixedEval pub z = (push rs).fixedEval pub u := by
      simp [push,Code.fixedEval,Code.evalNat,addressOp,unit,u]
    rw [head,ih u hu htail,hmap]
    simp [u,write,Function.update_idem,Nat.add_assoc,Nat.add_comm 1]

private theorem push_safe (pub : Arg → ℕ) (w : ℕ) (z : NatState) (rs : List Reg)
    (unit : z.reg 42 = 1) (fit : z.reg 28 + rs.length < 2^w) :
    (push rs).fixedSafe w pub z := by
  induction rs generalizing z with
  | nil => trivial
  | cons r rs ih =>
    let u : NatState := ⟨Function.update z.reg 28 (z.reg 28+1),
      Function.update z.mem (z.reg 28) (z.reg r)⟩
    have hu : u.reg 42 = 1 := by simpa [u] using unit
    have hf : u.reg 28 + rs.length < 2^w := by simpa [u,Nat.add_assoc,Nat.add_comm 1] using fit
    have tail := ih u hu hf
    simp only [push,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,addressOp,addressOpFits,
      unit,true_and]
    exact ⟨by simp only [List.length_cons] at fit; omega,tail⟩

/-- Input register values, before reading the sidecar's count. -/
structure Frame where
  /-- First staging lane in a one-copy box. -/
  orig : ℕ
  /-- Base of the decoded sidecar words. -/
  side : ℕ
  /-- Number of copies in the bottom bundle. -/
  copies : ℕ
  /-- First externally guessed use lane. -/
  useStart : ℕ
  /-- Base of the box inside the assignment bank. -/
  base : ℕ
  /-- Physical copy stride, including the reserved suffix. -/
  stride : ℕ
  /-- Reserved staging lanes per copy. -/
  cap : ℕ
  /-- First free output word. -/
  dst : ℕ
  /-- Number of records previously emitted. -/
  previousRows : ℕ

/-- The static ABI inputs held through all loop iterations. -/
def Frame.static (f : Frame) (z : NatState) : Prop :=
  z.reg 19 = f.orig ∧ z.reg 20 = f.side ∧ z.reg 21 = f.copies ∧
  z.reg 25 = f.base ∧ z.reg 26 = f.stride ∧ z.reg 27 = f.cap

/-- The frozen register interface at the start of the fragment. -/
def Frame.loaded (f : Frame) (z : NatState) : Prop :=
  f.static z ∧ z.reg 24 = f.useStart ∧ z.reg 28 = f.dst ∧ z.reg 29 = f.previousRows

/-- Sidecar input and supplemental output are disjoint, and all reached indices fit. -/
structure Frame.Fits (f : Frame) (w n : ℕ) (rel : ℕ → ℕ) : Prop where
  /-- Enough staging lanes for this site's weighted sources. -/
  count_le : n ≤ f.cap
  /-- The last sidecar word can be addressed. -/
  side_end : f.side+3*n < 2^w
  /-- The one-past-end output cursor can be represented. -/
  dst_end : f.dst+9*n+6 < 2^w
  /-- The record count after emitting all bindings and the padding record fits. -/
  count_end : f.previousRows+n+1 < 2^w
  /-- The compact use cursor after the last copy fits. -/
  use_end : f.useStart+n*f.copies < 2^w
  /-- The unused suffix starts at an address representable even when it is empty. -/
  padding_base : f.base+(f.orig+n) < 2^w
  /-- Every listed relative lane translates to a bank address. -/
  row_base : ∀ i < n, f.base+rel i < 2^w
  /-- Writing output cannot overwrite an unread sidecar word. -/
  disjoint : f.side+3*n < f.dst ∨ f.dst+9*n+6 ≤ f.side

/-- Equality tying a staged lane to the external guesses for all copies. -/
def Frame.equalRow (f : Frame) (i rel : ℕ) : Record :=
  .equal f.copies 1 (stagedPort f.base f.stride rel) (usePort (f.useStart+i*f.copies))

/-- Exactly one row pins the whole unused suffix. -/
def Frame.zeroRow (f : Frame) (n : ℕ) : Record :=
  .zero f.copies (f.cap-n) (stagedPort f.base f.stride (f.orig+n))

/-- Prefix of rows already emitted by the source scan. -/
def Frame.rows (f : Frame) (rel : ℕ → ℕ) : ℕ → List Record
  | 0 => []
  | i+1 => f.rows rel i ++ [f.equalRow i (rel i)]

/-- The prefix occupies exactly nine words per source regardless of the bundle multiplicity. -/
theorem Frame.rows_words_length (f : Frame) (rel : ℕ → ℕ) (n : ℕ) :
    ((f.rows rel n).flatMap Packet.record).length = 9*n := by
  induction n with
  | zero => simp [rows]
  | succ n ih => simp [rows,ih,equalRow,Packet.record,Packet.port,Nat.mul_succ]

/-- The fragment never touches the other caller registers in any successful run. -/
theorem program_keeps {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m es t mt} (run : Runs pub mac program s m es t mt)
    (r : Reg) (hr : r.val < 40) (h24 : r ≠ 24) (h28 : r ≠ 28) (h29 : r ≠ 29) : t r = s r := by
  have h : ∀ i : Reg, i.val < 40 → i ≠ 24 → i ≠ 28 → i ≠ 29 → program.keeps i = true := by decide
  exact run.keepsReg (h r hr h24 h28 h29)

end Packing.BottomReports.Writer

end BorderVNP
end Computability
end OAI
