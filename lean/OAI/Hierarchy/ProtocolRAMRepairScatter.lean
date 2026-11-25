import OAI.Hierarchy.ProtocolRAMRepairOrdinal
import OAI.Hierarchy.ProtocolRAMRowChoice
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProtocolRAMWeightedScatter

namespace OAI
/-! # Native signed occurrence scatter for commodity and physical edge banks -/

namespace Hierarchy.ProtocolRAM.RepairHistogram
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing
variable {w n : ℕ}

/-- Each option carries a commodity ordinal or the ordinary-link sentinel `goods`.
Out-of-range selector words go to the same disposable cell, so they cannot overwrite
history or another bank. -/
def destination (base goods : ℕ) (slot : Expr) : Expr :=
  .op .add (.lit base) (.branch .lt slot (.lit goods) slot (.lit goods))

theorem destination_val (base goods : ℕ) (slot : Expr) (m : Memory w) (r : Word w) (fit : base+goods<2^w) :
    ((destination base goods slot).eval m r).val=base+min (slot.eval m r).val goods := by
  have g : goods<2^w := by omega
  let t := slot.eval m r
  change ((base : Word w) + (if decide (t < (goods : Word w)) then t else (goods : Word w))).val = _
  have test : (t < (goods : Word w)) ↔ t.val < goods := by
    change t.val < (goods : Word w).val ↔ _
    rw [Fin.val_cast_of_lt g]
  by_cases small : t.val < goods
  · simp only [decide_eq_true_eq, ite_eq_left (test.mpr small)]
    rw [show t = ((t.val : ℕ) : Word w) from (Fin.cast_val_eq_self t).symm, ← Nat.cast_add]
    rw [Fin.val_cast_of_lt (show base+t.val<2^w by omega)]
    exact (congrArg (base+·) (min_eq_left small.le)).symm
  · simp only [decide_eq_true_eq, ite_eq_right (fun ht => small (test.mp ht)), ← Nat.cast_add,
      Fin.val_cast_of_lt fit]
    exact (congrArg (base+·) (min_eq_right (Nat.le_of_not_lt small))).symm

def pair (p : Columns) : Expr :=
  let index := Expr.lookup p.occurrence .row
  .branch .eq (.lookup p.isData .row) (.lit 0) (p.destination.atRow index)
    (.op .sub (p.credit.atRow index) (p.charge.atRow index))

def installedBits (p : Columns) (m : Memory w) (i : Fin n) := (p.credit.eval m (i.val:Word w)).val

def consumedBits (p : Columns) (m : Memory w) (i : Fin n) := (p.charge.eval m (i.val:Word w)).val

def address (p : Columns) (m : Memory w) (i : Fin n) := (p.destination.eval m (i.val:Word w)).val

def delta (p : Columns) (m : Memory w) (i : Fin n) :=
  (p.credit.eval m (i.val:Word w) - p.charge.eval m (i.val:Word w)).val

def code (w src n : ℕ) (p : Columns) : Procedure w :=
  (scan w src (2*n) (pair p)).seq (ProtocolRAMWeightedScatter.program w src n)

def ticks (n : ℕ) (p : Columns) := (4+2*n*(2*(pair p).work+4))+(3+12*n)

def result (p : Columns) (src n : ℕ) (m : Memory w) : Memory w :=
  ProtocolRAMWeightedScatter.image (address (n:=n) p m) (delta p m) (image src (2*n) (pair p) m) n

theorem run (p : Columns) (src n : ℕ) (m : Memory w) (directory : PairDirectory p m n)
    (before : (pair p).Fits w src) (room : src+2*n<2^w) (safe : ∀ i : Fin n,address p m i<src) :
    (code w src n p).Exec m (result p src n m) (ticks n p) := by
  let inter := image src (2*n) (pair p) m
  have gen : (scan w src (2*n) (pair p)).Exec m inter (4+2*n*(2*(pair p).work+4)) :=
    scan_exec src (2*n) (pair p) m before room
  apply gen.then
  apply ProtocolRAMWeightedScatter.run src (address p m) (delta p m) inter room.le
    (fun i => (safe i).trans (by omega)) (fun i => .inl (safe i))
  intro i
  have hi := i.isLt
  have a := ProtocolRAMGeneratedWrite.read_image src (2*n) (pair p) m ⟨2*i.val,by omega⟩
  have z := ProtocolRAMGeneratedWrite.read_image src (2*n) (pair p) m ⟨2*i.val+1,by omega⟩
  constructor
  · rw [show inter (src+2*i.val)=(pair p).eval m ((2*i.val:ℕ):Word w) from a]
    simp only [pair, Expr.eval, Comparison.test, eval_atRow, Nat.cast_zero, beq_iff_eq, directory.first i,
      directory.firstRow i, ite_true, address, Fin.cast_val_eq_self]
  · rw [show inter (src+2*i.val+1)=(pair p).eval m ((2*i.val+1:ℕ):Word w) by simpa [Nat.add_assoc] using z]
    simp only [pair, Expr.eval, Comparison.test, eval_atRow, Nat.cast_zero, beq_iff_eq, directory.second i,
      directory.secondRow i, ite_false, delta, RowOp.opcode, BinaryOp.eval, Fin.cast_val_eq_self]

end Hierarchy.ProtocolRAM.RepairHistogram

end OAI
