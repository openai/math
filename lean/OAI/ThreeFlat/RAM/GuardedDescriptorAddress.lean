import OAI.ThreeFlat.RAM.GuardedDescriptor
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Abel

namespace OAI
/-! # Decoding the absolute addresses of guarded cell records -/

namespace ThreeFlat.RAM.GuardedDescriptor

open Computability.VPVNP.BurstRAM PrivateRAM
open DescriptorExpr
open scoped Fin.CommRing

variable {w : ℕ}

def recordAddress (base copied guards block localCell col : ℕ) : ℕ :=
  base + (11 * (block * (copied+guards) + localCell) + col)

private theorem div_nat (x d : ℕ) (hx : x < 2^w) (hd : d < 2^w) :
    BinaryOp.eval .div (x : Word w) (d : Word w) = ((x/d : ℕ) : Word w) := by
  simp [BinaryOp.eval, Fin.val_cast_of_lt hx, Fin.val_cast_of_lt hd]

private theorem mod_nat (x d : ℕ) (hx : x < 2^w) (hd : d < 2^w) :
    BinaryOp.eval .mod (x : Word w) (d : Word w) = ((x%d : ℕ) : Word w) := by
  simp [BinaryOp.eval, Fin.val_cast_of_lt hx, Fin.val_cast_of_lt hd]

/-- In the valid record range the two quotient/remainder operations recover
the copied block number, local cell and column, including the guard offset
for cells after the copied part. -/
theorem coordinates_record (p : Inputs (Word w)) (base copied guards block localCell col : ℕ)
    (ha : p.address = (recordAddress base copied guards block localCell col : Word w))
    (hb : p.cellsBase = (base : Word w)) (hc : p.oldCells = (copied : Word w))
    (hg : p.guards = (guards : Word w)) (hcol : col < 11) (hi : localCell < copied+guards)
    (hwidth : copied+guards < 2^w) (h11 : 11 < 2^w)
    (fit : recordAddress base copied guards block localCell col < 2^w) :
    let c := coordinates (wordOps w) p
    c.block = (block : Word w) ∧ c.localCell = (localCell : Word w) ∧ c.col = (col : Word w) ∧
      (copied ≤ localCell → c.guardIndex = ((localCell-copied : ℕ) : Word w)) := by
  let width := copied+guards
  let row := block * width + localCell
  let off := 11*row + col
  have hf : base + off < 2^w := fit
  have hoff : off < 2^w := by omega
  have hrow : row < 2^w := by dsimp [off] at hoff; omega
  have offeq : BinaryOp.eval .sub p.address p.cellsBase = (off : Word w) := by
    rw [ha,hb]
    change ((base+off : ℕ) : Word w) - (base : Word w) = _
    simp
  have widtheq : BinaryOp.eval .add p.oldCells p.guards = (width : Word w) := by
    rw [hc,hg]
    simp [BinaryOp.eval,width]
  have roweq : off / 11 = row := by
    simp [off,Nat.mul_add_div (by decide : 0 < 11),Nat.div_eq_of_lt hcol]
  have coleq : off % 11 = col := by simp [off,Nat.mod_eq_of_lt hcol]
  have hlocal : localCell < width := hi
  have beq : row / width = block := by
    rw [show row = width*block+localCell by simp [row,Nat.mul_comm block width],
      Nat.mul_add_div (Nat.zero_lt_of_lt hlocal),Nat.div_eq_of_lt hlocal,Nat.add_zero]
  have ieq : row % width = localCell := by simp [row,Nat.mod_eq_of_lt hlocal]
  let ow := BinaryOp.eval .sub p.address p.cellsBase
  let dw := BinaryOp.eval .add p.oldCells p.guards
  let cw := BinaryOp.eval .div ow ((11 : ℕ) : Word w)
  have crow : cw = (row : Word w) := by
    dsimp only [cw,ow]
    rw [offeq,div_nat _ _ hoff h11,roweq]
  have bword : BinaryOp.eval .div cw dw = (block : Word w) := by
    dsimp only [dw]
    rw [crow,widtheq,div_nat _ _ hrow hwidth,beq]
  have lword : BinaryOp.eval .mod cw dw = (localCell : Word w) := by
    dsimp only [dw]
    rw [crow,widtheq,mod_nat _ _ hrow hwidth,ieq]
  have cword : BinaryOp.eval .mod ow ((11 : ℕ) : Word w) = (col : Word w) := by
    dsimp only [ow]
    rw [offeq,mod_nat _ _ hoff h11,coleq]
  refine ⟨bword,lword,cword,?_⟩
  intro h
  change BinaryOp.eval .mod cw dw - p.oldCells = _
  rw [lword,hc,Nat.cast_sub h]

/-- On copied cells, a coefficient word passes through the copy unchanged.
For sources there are three cases, literal, exposed pin and private bit. -/
theorem finish_copy (p : Inputs (Word w)) (c : Coordinates (Word w)) (raw pin left right : Word w)
    (hc : c.localCell < p.oldCells) :
    finish (wordOps w) p c raw pin left right =
      if c.col < (3 : Word w) then
        if raw < (2 : Word w) then raw else if raw < 2 + p.oldPins then pin else
          2 + p.globalPins + p.shared + c.block * p.oldHidden + (raw-(2+p.oldPins))
      else raw := by
  simp [finish,wordOps,Comparison.test,BinaryOp.eval,hc]

/-- The first three guard words give its two endpoints and a constant zero bit.
The remaining eight words encode equality of the two low label bits. -/
theorem finish_guard (p : Inputs (Word w)) (c : Coordinates (Word w)) (raw pin left right : Word w)
    (hc : p.oldCells ≤ c.localCell) :
    finish (wordOps w) p c raw pin left right =
      if c.col = (0 : Word w) then left else if c.col = (1 : Word w) then right else
      if c.col = (2 : Word w) then 0 else
        let u := c.col-3
        let x := BinaryOp.eval .mod u (2 : Word w)
        let y := BinaryOp.eval .mod (BinaryOp.eval .div u (2 : Word w)) (2 : Word w)
        if x = y then p.unitCode else p.zeroCode := by
  simp [finish,wordOps,Comparison.test,BinaryOp.eval,not_lt_of_ge hc]
  rfl

/-- The coefficient column indexes the bit triple in little-endian order. -/
theorem finish_guard_coeff (p : Inputs (Word w)) (c : Coordinates (Word w))
    (raw pin left right : Word w) (hc : p.oldCells ≤ c.localCell) (j : ℕ)
    (hj : j < 8) (hcol : c.col = ((3+j : ℕ) : Word w)) (fits : 11 < 2^w) :
    finish (wordOps w) p c raw pin left right =
      if j % 2 = (j/2)%2 then p.unitCode else p.zeroCode := by
  rw [finish_guard p c raw pin left right hc,hcol]
  have hj' : 3+j < 2^w := by omega
  have hval := Fin.val_cast_of_lt hj'
  have same (n : ℕ) (hn : n < 3) : ((3+j : ℕ) : Word w) ≠ (n : Word w) := by
    intro h
    have eqn := congrArg Fin.val h
    rw [hval, Fin.val_cast_of_lt (show n < 2^w by omega)] at eqn
    omega
  have sub : ((3+j : ℕ) : Word w) - 3 = (j : Word w) := by push_cast; abel
  have h2 : 2 < 2^w := by omega
  have hzero : ((3+j : ℕ) : Word w) ≠ 0 := same 0 (by decide)
  have hone : ((3+j : ℕ) : Word w) ≠ 1 := same 1 (by decide)
  have htwo : ((3+j : ℕ) : Word w) ≠ 2 := same 2 (by decide)
  rw [ite_eq_right hzero,ite_eq_right hone,ite_eq_right htwo]
  have hd : BinaryOp.eval .div (j : Word w) 2 = ((j/2 : ℕ) : Word w) :=
    div_nat j 2 (by omega) h2
  have hx : BinaryOp.eval .mod (j : Word w) 2 = ((j%2 : ℕ) : Word w) :=
    mod_nat j 2 (by omega) h2
  have hy : BinaryOp.eval .mod ((j/2 : ℕ) : Word w) 2 = (((j/2)%2 : ℕ) : Word w) :=
    mod_nat (j/2) 2 (by omega) h2
  rw [sub]
  change (if BinaryOp.eval .mod (j : Word w) 2 =
      BinaryOp.eval .mod (BinaryOp.eval .div (j : Word w) 2) 2 then _ else _) = _
  rw [hd,hx,hy]
  have sameWord : ((j%2 : ℕ) : Word w) = (((j/2)%2 : ℕ) : Word w) ↔ j%2 = (j/2)%2 := by
    rw [Fin.ext_iff,Fin.val_cast_of_lt (show j%2 < 2^w by omega),
      Fin.val_cast_of_lt (show (j/2)%2 < 2^w by omega)]
  simp only [sameWord]

end ThreeFlat.RAM.GuardedDescriptor

end OAI
