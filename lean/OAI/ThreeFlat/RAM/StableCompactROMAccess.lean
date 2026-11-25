import OAI.ThreeFlat.RAM.StableCompactProgram

namespace OAI
/-! # Fixed row-major address arithmetic for three-word template ROM entries -/

namespace ThreeFlat.RAM.StableCompactROMProgram

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr
open scoped Fin.CommRing

variable {w k : ℕ}

/-- The four incoming registers contain key, padded width, logical width and ROM base. -/
private def row : Term w k 4 := .binary .div (.result 0) (.literal 4)
def siteProgram : Term w k 4 := .binary .mod row (.result 1)
def pointerProgram : Term w k 4 :=
  .binary .add (.result 3) (.binary .mul (.literal 3)
    (.binary .add (.binary .mul (.literal 4) (.binary .div row (.result 1)))
      (.binary .mod (.result 0) (.literal 4))))

theorem siteProgram_binds : (siteProgram (w:=w) (k:=k)).binds = 3 := by
  simp [siteProgram,row,Term.binary,Term.literal,Term.binds]

theorem pointerProgram_binds : (pointerProgram (w:=w) (k:=k)).binds ≤ 14 := by
  simp [pointerProgram,row,Term.binary,Term.literal,Term.binds]

private theorem divWord (x d : ℕ) (hx : x < 2^w) (hd : d < 2^w) :
    BinaryOp.eval .div (x : Word w) (d : Word w) = ((x/d : ℕ) : Word w) := by
  simp [BinaryOp.eval,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hd]

private theorem modWord (x d : ℕ) (hx : x < 2^w) (hd : d < 2^w) :
    BinaryOp.eval .mod (x : Word w) (d : Word w) = ((x%d : ℕ) : Word w) := by
  simp [BinaryOp.eval,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hd]

theorem addresses_eval (N base t v : ℕ) (j : Fin 4) (hv : v < N) (four : 4 < 2^w)
    (sites : N < 2^w) (keyfit : 4*(t*N+v)+j.val < 2^w)
    (words : Fin k → Word w) (mem : Memory w) (vs : Fin 4 → Word w)
    (key : vs 0 = ((4*(t*N+v)+j.val : ℕ) : Word w)) (width : vs 1 = (N : Word w))
    (ptr : vs 3 = (base : Word w)) :
    pointerProgram.eval words mem vs = ((base+3*(4*t+j.val) : ℕ) : Word w) ∧
    siteProgram.eval words mem vs = (v : Word w) := by
  let r := t*N+v
  have hrow : (4*r+j.val)/4 = r := by simp [Nat.mul_add_div (by decide : 0<4),Nat.div_eq_of_lt j.isLt]
  have hcolumn : (4*r+j.val)%4 = j.val := by simp [Nat.mod_eq_of_lt j.isLt]
  have ht : r/N = t := by
    dsimp [r]
    rw [Nat.mul_comm t, Nat.mul_add_div (Nat.zero_lt_of_lt hv),Nat.div_eq_of_lt hv,Nat.add_zero]
  have hsite : r%N = v := by simp [r,Nat.mod_eq_of_lt hv]
  have hr : r < 2^w := by change 4*r+j.val < 2^w at keyfit; omega
  have er : (row : Term w k 4).eval words mem vs = (r : Word w) := by
    simp only [row,Term.eval_binary,Term.eval_literal,Term.eval,key]
    exact (divWord (4*r+j.val) 4 keyfit four).trans (congrArg (fun a : ℕ => (a : Word w)) hrow)
  have ec : BinaryOp.eval .mod ((4*(t*N+v)+j.val : ℕ) : Word w) 4 = (j.val : Word w) :=
    (modWord (4*r+j.val) 4 keyfit four).trans (congrArg (fun a : ℕ => (a : Word w)) hcolumn)
  constructor
  · simp only [pointerProgram,Term.eval_binary,Term.eval_literal,Term.eval,key,width,ptr,er,ec,
      divWord r N hr sites,ht]
    simp [BinaryOp.eval]
  · simp only [siteProgram,Term.eval_binary,Term.eval,width,er,modWord r N hr sites,hsite]

end ThreeFlat.RAM.StableCompactROMProgram

end OAI
