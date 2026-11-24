import OAI.Computability.VPVNP.CompressorShrinkSliceArrays
import OAI.Computability.VPVNP.CompressorRecordsShrinkRAM

/-!
# Native equal-piece widths and prefix offsets for all AB bundles

The source index enumerates the piece ranks of each bundle consecutively.
One probe retrieves its total thick width. Two writes give the width and
prefix offset of this particular piece. Division by zero at a zero remainder
implements the zero indicator in the machine's prescribed word arithmetic.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ABWidths

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression
open ShrinkRAM (div mod select)
open scoped Fin.CommRing

variable {w : ℕ}

/-- Public words give the number of pieces, rectangle stride, total-width column,
AB width and AB offset bases. The latter two rectangles share their row stride. -/
def visit : List (Op 13 5) :=
  [.stateWord 0, .publicWord 1 0, .binary .div 2 0 1, .binary .mod 3 0 1,
   .publicWord 4 2, .binary .add 4 4 2, .read 5 4, .binary .div 6 5 1, .binary .mod 7 5 1,
   .constant 8 1, .binary .add 9 3 8, .binary .div 9 7 9, .binary .div 9 9 9,
   .binary .add 10 6 9, .binary .sub 11 3 7, .binary .mul 11 9 11, .binary .add 11 7 11,
   .binary .mul 6 3 6, .binary .add 11 6 11, .publicWord 6 1, .binary .mul 2 2 6,
   .binary .add 2 2 3, .publicWord 4 3, .binary .add 4 4 2, .write 4 10,
   .publicWord 4 4, .binary .add 4 4 2, .write 4 11, .binary .add 0 0 8]

/-- Recover the bundle number from the linear piece cursor by dividing by the number of pieces
per bundle. -/
def row (p : Fin 5 → Word w) (i : Word w) := div i (p 0)
/-- Recover the piece's rank within its bundle as the remainder of the linear cursor. -/
def rank (p : Fin 5 → Word w) (i : Word w) := mod i (p 0)
/-- Address of the selected bundle's total-width word in the input column. -/
def input (p : Fin 5 → Word w) (i : Word w) := p 2+row p i
/-- Address of a piece's width or offset in the corresponding output rectangle, using the
bundle stride and piece rank. -/
def address (p : Fin 5 → Word w) (t : Fin 2) (i : Word w) :=
  p (t.natAdd 3)+(row p i*p 1+rank p i)

/-- The machine-word indicator that this rank receives one of the extra units left over after
dividing the bundle width. -/
def extra (b q r : Word w) :=
  let t := div (mod b q) (r+1)
  div t t

/-- The sum of the widths assigned to earlier pieces, including their share of the division
remainder. -/
def offset (b q r : Word w) :=
  r * div b q + select (extra b q r) (mod b q) r

/-- The events for one AB-piece visit, including the read of the bundle total and the writes of
the piece width and prefix offset. -/
def events (p : Fin 5 → Word w) (m : Memory w) (i : Word w) : List (Event w) :=
  let t := m (input p i).val
  List.replicate 6 .tick ++ [.read (input p i) t] ++ List.replicate 17 .tick ++
    [.write (address p 0 i) (ShrinkSliceArrays.splitValue t (p 0) (rank p i)), .tick, .tick,
     .write (address p 1 i) (offset t (p 0) (rank p i)), .tick]

theorem native (p : Fin 5 → Word w) (m : Memory w) (i : Word w) :
    let M := (template visit 0).instantiate w p
    execute M.program 30 (M.program.start i) m [] = some ⟨events p m i, some (i+1)⟩ := by
  change execute ((template visit 0).instantiate w p).program (1+visit.length)
    ⟨_,i,fun _ ↦ 0,fun _ ↦ 0⟩ m [] = _
  rw [execute_template, run_eq_trace]
  rfl

theorem work (p : Fin 5 → Word w) (m : Memory w) (i : Word w) :
    (events p m i).length = 29 ∧ countProbes (events p m i) = 3 := ⟨rfl,rfl⟩

/-- Starting index of piece rank r in a balanced split. -/
def pieceStart (b q r : ℕ) := r*(b/q) + min r (b%q)

theorem prefix_succ (b q r : ℕ) (h : r < q) :
    pieceStart b q (r+1) = pieceStart b q r + splitWidth b q ⟨r,h⟩ := by
  unfold pieceStart splitWidth
  simp only [Nat.succ_mul]
  split <;> omega

theorem prefix_sum {b q : ℕ} (i : Fin q) :
    pieceStart b q i.val = PackingData.fieldStart (Equiv.refl (Fin q)) (splitWidth b q) i := by
  have aux (r : ℕ) (h : r ≤ q) : pieceStart b q r =
      ∑ t : Fin r, splitWidth b q (Fin.castLE h t) := by
    induction r with
    | zero => simp [pieceStart]
    | succ r ih =>
      rw [Fin.sum_univ_castSucc, prefix_succ b q r (by omega), ih (by omega)]
      rfl
  exact aux i.val i.isLt.le

private theorem div_val (a b : Word w) : (div a b).val = a.val/b.val :=
  Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt a.isLt)

private theorem mod_val (a b : Word w) : (mod a b).val = a.val%b.val :=
  Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt a.isLt)

theorem offset_exact (b q r : Word w) (h : r.val < q.val) :
    (offset b q r).val = pieceStart b.val q.val r.val := by
  have hp : 1 < 2^w := by have := q.isLt; omega
  have he : (r+1).val = r.val+1 := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt (by have := q.isLt; omega)]
  have hsum : pieceStart b.val q.val r.val ≤ b.val := by
    unfold pieceStart
    have ht := Nat.mul_le_mul_right (b.val/q.val) h.le
    have hd := Nat.div_add_mod b.val q.val
    have hm := min_le_right r.val (b.val%q.val)
    omega
  let t := div (mod b q) (r+1)
  have ht : t.val = b.val % q.val / (r.val+1) := by rw [div_val, mod_val, he]
  have hx : select (extra b q r) (mod b q) r = if r.val < b.val%q.val then r else mod b q := by
    by_cases hl : r.val < b.val%q.val
    · have ht' : 0 < t.val := ht ▸ Nat.div_pos (by omega) (Nat.zero_lt_succ _)
      have h1 : extra b q r = 1 := Fin.ext (by
        change (div t t).val = (1 : Word w).val
        rw [div_val,Nat.div_self ht', Fin.val_one',Nat.mod_eq_of_lt hp])
      simp [hl, h1]
    · have hz : t.val = 0 := ht.trans (Nat.div_eq_of_lt (by omega))
      have h0 : extra b q r = 0 := Fin.ext (by change (div t t).val = 0; rw [div_val,hz])
      simp [hl,h0]
  rw [offset,hx,Fin.val_add,Fin.val_mul,div_val,Nat.mod_add_mod]
  split
  · rename_i hl
    simpa only [pieceStart,min_eq_left hl.le] using
      Nat.mod_eq_of_lt (hsum.trans_lt b.isLt)
  · rename_i hl
    rw [mod_val]
    simpa only [pieceStart,min_eq_right (Nat.le_of_not_gt hl)] using
      Nat.mod_eq_of_lt (hsum.trans_lt b.isLt)

end CompressorRecords.ABWidths

end VPVNP
end Computability
end OAI
