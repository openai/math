import OAI.ThreeFlat.RAM.LiteralTable
import OAI.Computability.VPVNP.PrimedInputRAMOpcodeFields
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Native random access to a four-word row repeated across a Boolean cube -/

namespace ThreeFlat.RAM.StableCompactProgram
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr
open scoped Fin.CommRing

variable {m c w k n : ℕ}

/-- The address functions used by a replicated row. A site bit outside the cube is zero. -/
inductive Entry (m : ℕ) where
  | literal (value : ℕ)
  | siteBit (j : ℕ)
  | translated (base : ℕ) (mask : Fin (2^m))

def Entry.atSite (e : Entry m) (v : Fin (2^m)) : ℕ :=
  match e with
  | .literal z => z
  | .siteBit j => (v.val.testBit j).toNat
  | .translated base mask => base + (v.val ^^^ mask.val)

/-- Register zero holds the site. All constants belong to the single local row. -/
def Entry.program (e : Entry m) : Term w k 1 :=
  match e with
  | .literal z => .literal (z : Word w)
  | .siteBit j =>
    if j < m then
      .binary .bitAnd (.binary .shiftRight (.result 0) (.literal (j : Word w))) (.literal 1)
    else .literal 0
  | .translated base mask =>
    .binary .add (.literal (base : Word w))
      (.binary .bitXor (.result 0) (.literal (mask.val : Word w)))

theorem Entry.program_binds (e : Entry m) : (e.program (w := w) (k := k)).binds ≤ 4 := by
  cases e with
  | siteBit j =>
    by_cases hj : j < m <;> simp [program,hj,Term.binary,Term.literal,Term.binds]
  | _ => simp [program,Term.binary,Term.literal,Term.binds]

theorem Entry.program_eval (e : Entry m) (v : Fin (2^m)) (hw : 0 < w) (sites : 2^m < 2^w)
    (words : Fin k → Word w) (mem : Memory w) (vs : Fin 1 → Word w) (arg : vs 0 = (v.val : Word w)) :
    e.program.eval words mem vs = ((e.atSite v : ℕ) : Word w) := by
  have fitV := v.isLt.trans sites
  cases e with
  | literal z => simp [program,atSite]
  | translated base mask =>
    simp [program,atSite,Term.eval,arg,BinaryOp.eval,Fin.val_cast_of_lt fitV,
      Fin.val_cast_of_lt (mask.isLt.trans sites)]
  | siteBit j =>
    by_cases hj : j < m
    · have fitJ : j < 2^w := hj.trans (Nat.lt_two_pow_self.trans sites)
      simp only [program,ite_eq_left hj,Term.eval_binary,Term.eval_literal,Term.eval,arg]
      rw [Computability.VPVNP.PrimedInputRAM.Opcodes.readBit_word hw,Fin.val_cast_of_lt fitV,Fin.val_cast_of_lt fitJ]
      cases h : v.val.testBit j <;> simp [atSite,h,Computability.VPVNP.PrimedInputRAM.encodeBit]
    · have low : v.val < 2^j := v.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hj))
      simp [program,hj,atSite,Nat.testBit_lt_two_pow low]

/-- Physical rows are in site-fast order. Their compact columns are the three
source addresses and the scalar library number. -/
def address (t : Fin c) (v : Fin (2^m)) (j : Fin 4) : ℕ := 4*(t.val*2^m+v.val)+j.val

private def selectEntry (T : Fin c → Fin 4 → Entry m) (a : ℕ) : Entry m :=
  if h : a/4 < c then T ⟨a/4,h⟩ ⟨a%4,Nat.mod_lt _ (by decide)⟩ else .literal 0

private theorem selectEntry_at (T : Fin c → Fin 4 → Entry m) (t : Fin c) (j : Fin 4) :
    selectEntry T (4*t.val+j.val) = T t j := by
  have div : (4*t.val+j.val)/4 = t.val := by
    simp [Nat.mul_add_div (by decide : 0<4),Nat.div_eq_of_lt j.isLt]
  have rem : (4*t.val+j.val)%4 = j.val := by simp [Nat.mod_eq_of_lt j.isLt]
  simp [selectEntry,div,rem,t.isLt]

private def row : Term w k 1 := .binary .div (.result 0) (.literal 4)

private def site (m : ℕ) : Term w k 1 := .binary .mod row (.literal ((2^m : ℕ) : Word w))

private def index (m : ℕ) : Term w k 1 :=
  .binary .add (.binary .mul (.literal 4) (.binary .div row (.literal ((2^m : ℕ) : Word w))))
    (.binary .mod (.result 0) (.literal 4))

/-- Program size depends on the template, with no dependence on its replication count. -/
def program (T : Fin c → Fin 4 → Entry m) : Term w k 1 :=
  let choices : ℕ → Term w k 2 := fun a => (selectEntry T a).program.rename (fun _ => 1)
  (LiteralTable.dispatch 0 choices (4*c)).instantiate ![index m,site m]

theorem program_binds (T : Fin c → Fin 4 → Entry m) :
    (program (w:=w) (k:=k) T).binds ≤ 24*c+20 := by
  have choices := LiteralTable.dispatch_binds (w := w) (k := k) (n := 2) 0
    (fun a => (selectEntry T a).program.rename (fun _ => 1)) (4*c) 4
    (fun a _ => by simpa only [Term.binds_rename] using (selectEntry T a).program_binds (w:=w) (k:=k))
  unfold program
  rw [Term.binds_instantiate,Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,index,site,row,Term.binary,
    Term.binds_letThen,Term.binds_rename,Term.literal,Term.binds]
  omega

private theorem divWord (x d : ℕ) (hx : x < 2^w) (hd : d < 2^w) :
    BinaryOp.eval .div (x : Word w) (d : Word w) = ((x/d : ℕ) : Word w) := by
  simp [BinaryOp.eval,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hd]

private theorem modWord (x d : ℕ) (hx : x < 2^w) (hd : d < 2^w) :
    BinaryOp.eval .mod (x : Word w) (d : Word w) = ((x%d : ℕ) : Word w) := by
  simp [BinaryOp.eval,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hd]

theorem program_eval (T : Fin c → Fin 4 → Entry m) (t : Fin c) (v : Fin (2^m)) (j : Fin 4)
    (four : 4 < 2^w) (sites : 2^m < 2^w) (small : 4*c ≤ 2^w)
    (fit : address t v j < 2^w) (words : Fin k → Word w) (mem : Memory w)
    (vs : Fin 1 → Word w) (arg : vs 0 = (address t v j : Word w)) :
    (program T).eval words mem vs = ((T t j).atSite v : Word w) := by
  let r := t.val*2^m+v.val
  have hr : r < 2^w := by change 4*r+j.val < 2^w at fit; omega
  have hj : (4*r+j.val)%4 = j.val := by simp [Nat.mod_eq_of_lt j.isLt]
  have hrow : (4*r+j.val)/4 = r := by
    simp [Nat.mul_add_div (by decide : 0<4),Nat.div_eq_of_lt j.isLt]
  have ht : r/(2^m) = t.val := by
    unfold r
    rw [Nat.mul_comm t.val, Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt v.isLt,Nat.add_zero]
  have hv : r%(2^m) = v.val := by simp [r,Nat.mod_eq_of_lt v.isLt]
  have er : (row : Term w k 1).eval words mem vs = (r : Word w) := by
    simp only [row,Term.eval_binary,Term.eval,Term.eval_literal,arg]
    exact (divWord _ 4 fit four).trans (congrArg (fun z : ℕ => (z : Word w)) hrow)
  have ec : (site m : Term w k 1).eval words mem vs = (v.val : Word w) := by
    simp only [site,Term.eval_binary,Term.eval_literal,er,modWord r _ hr sites,hv]
  have ex : (index m : Term w k 1).eval words mem vs = ((4*t.val+j.val : ℕ) : Word w) := by
    simp only [index,Term.eval_binary,Term.eval_literal,Term.eval,arg,er,
      divWord r _ hr sites,ht]
    have col : BinaryOp.eval .mod (address t v j : Word w) 4 = (j.val : Word w) :=
      (modWord _ 4 fit four).trans (congrArg (fun z : ℕ => (z : Word w)) hj)
    rw [col]
    simp [BinaryOp.eval]
  let env : Fin 2 → Word w := fun i => (![index m,site m] i : Term w k 1).eval words mem vs
  have hkey : env 0 = ((4*t.val+j.val : ℕ) : Word w) := ex
  have hout : 4*t.val+j.val < 4*c := by have := t.isLt; have := j.isLt; omega
  have hw : 0<w := Nat.pos_of_ne_zero (fun eqn => by subst w; norm_num at four)
  rw [program,Term.eval_instantiate]
  change (LiteralTable.dispatch 0 _ _).eval _ _ env = _
  rw [LiteralTable.dispatch_eval (x:=4*t.val+j.val) (hx:=hout) (hs:=small) (arg:=hkey),
    Term.eval_rename,selectEntry_at]
  exact (T t j).program_eval v hw sites words mem _ ec

end ThreeFlat.RAM.StableCompactProgram

end OAI
