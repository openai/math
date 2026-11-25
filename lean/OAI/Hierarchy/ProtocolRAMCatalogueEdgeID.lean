import OAI.Hierarchy.ProtocolRAMCatalogueRowFields

namespace OAI
/-! # Resolving recorded physical link IDs at their original purchase -/

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing
variable {W : ℕ}

/-- Core rows occupy the fixed prefix. An acquired row is available exactly when
the authoritative flag of its original purchase is set. The one-past-end ordinal
targets the sparse scatter's disposable cell. -/
def Board.checkedEdge (b : Board) (x : Expr) : Expr :=
  .branch .lt x (.lit b.coreRows) x <|
    .branch .lt x (.lit b.rows)
      (.branch .eq (b.bought.flag.atRow (.op .sub x (.lit b.coreRows))) (.lit 0) (.lit b.rows) x)
      (.lit b.rows)

theorem Board.checkedEdge_val (b : Board) (x : Expr) (m : Memory W) (r : Word W)
    (room : b.rows<2^W) :
    ((b.checkedEdge x).eval m r).val =
      if (x.eval m r).val<b.coreRows then (x.eval m r).val
      else if (x.eval m r).val<b.rows then
        if b.bought.flag.eval m (x.eval m r-(b.coreRows:Word W))=0 then b.rows else (x.eval m r).val
      else b.rows := by
  have core : b.coreRows<2^W := by unfold rows at room;omega
  simp only [checkedEdge,Expr.eval,Comparison.test,Fin.lt_def,decide_eq_true_eq,beq_iff_eq,eval_atRow,
    RowOp.opcode,BinaryOp.eval,Nat.cast_zero,Fin.val_cast_of_lt core,Fin.val_cast_of_lt room]
  split_ifs <;> first | rfl | exact Fin.val_cast_of_lt room

private theorem Board.suffix_sub (b : Board) (j : Fin b.boughtRows) :
    ((b.coreRows+j.val:ℕ):Word W)-(b.coreRows:Word W)=(j.val:Word W) := by
  rw [Nat.cast_add]
  abel

theorem Board.checked_core (b : Board) (x : Expr) (m : Memory W) (r : Word W) (j : Fin b.coreRows)
    (room : b.rows<2^W) (hit : (x.eval m r).val=j.val) :
    (b.checkedEdge x).eval m r=(j.val:Word W) := by
  apply Fin.ext
  have fit : j.val<2^W := by have := j.isLt; unfold rows at room;omega
  rw [b.checkedEdge_val x m r room,hit,ite_eq_left j.isLt,Fin.val_cast_of_lt fit]

theorem Board.checked_bought (b : Board) (x : Expr) (m : Memory W) (r : Word W) (j : Fin b.boughtRows)
    (room : b.rows<2^W) (hit : (x.eval m r).val=(b.boughtIndex j).val)
    (openLink : b.bought.flag.eval m (j.val:Word W)≠0) :
    (b.checkedEdge x).eval m r=((b.boughtIndex j).val:Word W) := by
  have limit := (b.boughtIndex j).isLt
  have raw : x.eval m r=((b.coreRows+j.val:ℕ):Word W) := Fin.ext (hit.trans (Fin.val_cast_of_lt (limit.trans room)).symm)
  apply Fin.ext
  rw [b.checkedEdge_val x m r room,hit,ite_eq_right (by change ¬b.coreRows+j.val<b.coreRows;omega),
    ite_eq_left limit,raw,b.suffix_sub j,ite_eq_right openLink,Fin.val_cast_of_lt (limit.trans room)]

/-- No computed write can hit a dormant acquired physical edge. -/
theorem Board.checked_hit (b : Board) (x : Expr) (m : Memory W) (r : Word W) (j : Fin b.boughtRows)
    (room : b.rows<2^W) (hit : ((b.checkedEdge x).eval m r).val=(b.boughtIndex j).val) :
    b.bought.flag.eval m (j.val:Word W)≠0 := by
  have last := (b.boughtIndex j).isLt
  have start : b.coreRows≤(b.boughtIndex j).val := Nat.le_add_right _ _
  rw [b.checkedEdge_val x m r room] at hit
  split at hit
  · omega
  split at hit
  · split at hit
    · omega
    · rename_i live
      have raw : x.eval m r=((b.coreRows+j.val:ℕ):Word W) :=
        Fin.ext (hit.trans (Fin.val_cast_of_lt (last.trans room)).symm)
      rwa [raw,b.suffix_sub j] at live
  · omega

/-- The source candidate number is the original signed-stratum/DFS row in the
parent's purchase market. The fixed parent offset is set by the schedule. -/
def Board.originalProbe (b : Board) (birthStride birth : ℕ) (ball : Expr) : Expr :=
  .op .add (.lit (b.coreRows+birth*birthStride)) ball

theorem Board.originalProbe_read (b : Board) (stride birth : ℕ) (ball : Expr) (m : Memory W) (r : Word W)
    (j : Fin stride) (atBall : ball.eval m r=(j.val:Word W)) :
    (b.originalProbe stride birth ball).eval m r=((b.coreRows+(birth*stride+j.val):ℕ):Word W) := by
  change ((b.coreRows+birth*stride:ℕ):Word W)+ball.eval m r=_
  rw [atBall,←Nat.add_assoc]
  exact (Nat.cast_add _ _).symm

/-- Use these exact common IDs in both the posted price and the physical paid
width pass. Subtraction of the common base cancels as word arithmetic. -/
def Board.commonID (b : Board) (edge : Expr) : Expr := .op .add (.lit b.idBase) (b.checkedEdge edge)

theorem Board.commonID_sub (b : Board) (edge : Expr) (m : Memory W) (r : Word W) :
    (b.commonID edge).eval m r-(b.idBase:Word W)=(b.checkedEdge edge).eval m r := by
  change (b.idBase:Word W)+(b.checkedEdge edge).eval m r-(b.idBase:Word W)=_
  abel

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end OAI
