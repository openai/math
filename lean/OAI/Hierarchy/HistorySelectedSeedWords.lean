import OAI.ThreeFlat.RAM.HistoryInitialSeed

namespace OAI
/-! # Receiver leaf commands for contiguous scheduled factor inputs -/

namespace Hierarchy.HistorySelectedSeed
open ThreeFlat RAM RAM.DescriptorExpr RAM.HistoryInitialSeed
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {W k : ℕ}

/-- The control cursor and remaining scratch words while the corresponding job executes. -/
def ControlAt (A : Layout) (z : Site) (job : ℕ) (m : Memory W) :=
  m A.ctrl = ((A.ctrl+2+7*job : ℕ) : Word W) ∧
  (∀ i : Fin 42, (0 : ℕ) < i.val → m (A.ctrl+i.val) = (z.words A i : Word W))

private def cell (A : Layout) (j : ℕ) : Term W k 1 := Term.load (Term.literal ((A.ctrl+j : ℕ) : Word W))
private def lit (n : ℕ) : Term W k 1 := .literal (n : Word W)

private def args (A : Layout) : Fin 4 → Term W k 1 :=
  let delta := Term.binary .sub (.result 0) (cell A 27)
  ![.binary .div delta (lit 4),.binary .mod delta (lit 4),cell A 24,cell A 25]

/-- The same generated operator handles the three dynamic ranges. The interval header's
last word is the first scheduled slot of this original lane on the current receiver tape. -/
def words (A : Layout) (dec : Term W k 4) : Term W k 1 :=
  let atCmd := cell A 0
  let key : Term W k 1 := .result 0
  let laneStart := (Term.binary .add (cell A 31) (lit 3)).load
  let endpoint := Term.binary .add (.binary .add (lit 2) laneStart) (.binary .sub key (cell A 29))
  let header := (Term.binary .add (lit (A.ctrl+36)) (.binary .sub key (cell A 33))).load
  .select .eq atCmd (lit (A.ctrl+2)) (dec.instantiate (args A))
    (.select .eq atCmd (lit (A.ctrl+9)) endpoint header)

private theorem control_val (A : Layout) (z : Site) (m : Memory W) (job j : ℕ)
    (data : Fin k → Word W) (a : Word W) (ctl : ControlAt A z job m)
    (room : A.ctrl+42<2^W) (pos : 0<j) (hj : j<42) :
    (cell A j).eval data m (fun _ => a)=(z.words A ⟨j,hj⟩ : Word W) := by
  simp only [cell,Term.eval_load,Term.eval_literal,Fin.val_cast_of_lt (by omega : A.ctrl+j<2^W)]
  exact ctl.2 ⟨j,hj⟩ pos

private theorem command (A : Layout) (z : Site) (m : Memory W) (job : ℕ)
    (data : Fin k → Word W) (a : Word W) (ctl : ControlAt A z job m) (room : A.ctrl+42<2^W) :
    (cell A 0).eval data m (fun _ => a)=((A.ctrl+2+7*job:ℕ):Word W) := by
  simpa [cell,Fin.val_cast_of_lt (by omega : A.ctrl<2^W)] using ctl.1

private theorem diff {x y : ℕ} (xs : x<2^W) (ys : y<2^W) (neq : x≠y) :
    (x:Word W)≠(y:Word W) := by
  intro eqn
  exact neq (by simpa only [Fin.val_cast_of_lt xs,Fin.val_cast_of_lt ys] using congrArg Fin.val eqn)

theorem first_word (A : Layout) (z : Site) (dec : Term W k 4) (pub : Fin k → Word W)
    (m : Memory W) (a : Word W) (ctl : ControlAt A z 0 m) (room : A.ctrl+42<2^W) :
    let delta := a-(z.stream A:Word W)
    (words A dec).eval pub m (fun _ => a)=dec.eval pub m
      ![BinaryOp.eval .div delta 4,BinaryOp.eval .mod delta 4,(z.lane:Word W),(z.stage:Word W)] := by
  have ctr := command A z m 0 pub a ctl room
  have dst := control_val A z m 0 27 pub a ctl room (by decide) (by decide)
  have lane := control_val A z m 0 24 pub a ctl room (by decide) (by decide)
  have age := control_val A z m 0 25 pub a ctl room (by decide) (by decide)
  change _=(z.stream A:Word W) at dst
  change _=(z.lane:Word W) at lane
  change _=(z.stage:Word W) at age
  simp only [words,Term.eval_select,ctr,lit,Term.eval_literal,Nat.mul_zero,Nat.add_zero,
    Comparison.test,beq_self_eq_true,ite_true,Term.eval_instantiate]
  congr 1
  funext i
  fin_cases i <;> simp [args,lit,dst,lane,age,Term.eval,BinaryOp.eval]

theorem endpoint_word (A : Layout) (z : Site) (dec : Term W k 4) (pub : Fin k → Word W)
    (m : Memory W) (a : Word W) (ctl : ControlAt A z 1 m) (room : A.ctrl+42<2^W)
    (fit : A.intervals+4*z.lane+3<2^W) :
    (words A dec).eval pub m (fun _ => a)=
      2+m (A.intervals+4*z.lane+3)+(a-(z.extBase A:Word W)) := by
  have ctr := command A z m 1 pub a ctl room
  have dst := control_val A z m 1 29 pub a ctl room (by decide) (by decide)
  have lane := control_val A z m 1 31 pub a ctl room (by decide) (by decide)
  change _=(z.extBase A:Word W) at dst
  change _=((A.intervals+4*z.lane:ℕ):Word W) at lane
  rw [show A.ctrl+2+7*1=A.ctrl+9 by omega] at ctr
  have ne := diff (W:=W) (x:=A.ctrl+9) (y:=A.ctrl+2) (by omega) (by omega) (by omega)
  simp only [words,Term.eval_select,ctr,lit,Term.eval_literal,Comparison.test,
    beq_iff_eq,ne,ite_false,ite_true,Term.eval_load,Term.eval_binary,lane,dst,Term.eval]
  change 2 + m ((((A.intervals+4*z.lane : ℕ):Word W)+3).val) + _=_
  rw [show (((A.intervals+4*z.lane:ℕ):Word W)+3)=((A.intervals+4*z.lane+3:ℕ):Word W) by simp only [Nat.cast_add,Nat.cast_ofNat],
    Fin.val_cast_of_lt fit]
  rfl

theorem result_word (A : Layout) (z : Site) (dec : Term W k 4) (pub : Fin k → Word W)
    (m : Memory W) (j : Fin 6) (ctl : ControlAt A z 2 m) (room : A.ctrl+42<2^W) :
    (words A dec).eval pub m (fun _ => ((z.resultBase A+j.val:ℕ):Word W))=
      (z.words A ⟨36+j.val,by omega⟩:Word W) := by
  let a : Word W := ((z.resultBase A+j.val:ℕ):Word W)
  have ctr := command A z m 2 pub a ctl room
  have dst := control_val A z m 2 33 pub a ctl room (by decide) (by decide)
  change _=(z.resultBase A:Word W) at dst
  rw [show A.ctrl+2+7*2=A.ctrl+16 by omega] at ctr
  have ne := diff (W:=W) (x:=A.ctrl+16) (y:=A.ctrl+2) (by omega) (by omega) (by omega)
  have ne' := diff (W:=W) (x:=A.ctrl+16) (y:=A.ctrl+9) (by omega) (by omega) (by omega)
  change (words A dec).eval pub m (fun _ => a)=_
  simp only [words,Term.eval_select,ctr,lit,Term.eval_literal,Comparison.test,
    beq_iff_eq,ne,ne',ite_false,Term.eval_load,Term.eval_binary,dst,Term.eval]
  change m ((((A.ctrl+36:ℕ):Word W)+(a-(z.resultBase A:Word W))).val)=_
  have δ : a-(z.resultBase A:Word W)=(j.val:Word W) := by
    dsimp [a]
    rw [Nat.cast_add,add_sub_cancel_left]
  rw [δ,←Nat.cast_add,Fin.val_cast_of_lt (by have := j.isLt; omega)]
  simpa only [Nat.add_assoc] using ctl.2 (⟨36+j.val, by omega⟩ : Fin 42) (by dsimp; omega)

/-- Instruction count of the new contiguous source and control operations. -/
theorem words_binds (A : Layout) (dec : Term W k 4) :
    (words A dec).binds≤dec.binds+128 := by
  simp [words,cell,lit,args,Term.select,Term.binary,Term.load,Term.literal,Term.binds,
    Term.binds_instantiate,Fin.sum_univ_succ]; omega

end Hierarchy.HistorySelectedSeed

end OAI
