import OAI.Hierarchy.ProtocolRAMBatch
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Compiling local decisions to the common endpoint descriptor array -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing

variable {w q d : ℕ}

/-- Seven live fields plus a zero padding word in each physical row. Both the row
quotient and the field selector are obtained by native bit operations. -/
def packed (owners : Bank) (fields : Fin 7 → Expr) : Expr :=
  chooseField 7 0 (fun j => (fields j).atRow (.lookup owners .row))
    (.op .mask .row (.lit 7))

/-- The fixed row-directory advice occupies exactly eight words per physical record. -/
def ownerAdvice (owners : Bank) (n : ℕ) (m : Memory w) : Memory w :=
  fillSegment owners.base (8*n) (fun a => ((a-owners.base)/8 : ℕ)) m

def Owners (owners : Bank) (n : ℕ) (m : Memory w) : Prop :=
  ∀ i : Fin n, ∀ j : Fin 8, owners.read m ((8*i.val+j.val : ℕ) : Word w) = (i.val:Word w)

theorem ownerAdvice_correct (owners : Bank) (n : ℕ) (m : Memory w)
    (room : 8*n < 2^w) (capacity : 8*n ≤ owners.size) : Owners owners n (ownerAdvice owners n m) := by
  intro i j
  have hi := i.isLt
  have hj := j.isLt
  have fit : 8*i.val+j.val < 2^w := by omega
  have small : 8*i.val+j.val < owners.size := by omega
  have inside : owners.base ≤ owners.base+(8*i.val+j.val) ∧
      owners.base+(8*i.val+j.val)<owners.base+8*n := by omega
  simp only [Bank.read,Fin.val_cast_of_lt fit,Nat.mod_eq_of_lt small,ownerAdvice,
    fillSegment,ite_eq_left inside,Nat.add_sub_cancel_left]
  congr 1
  omega

private theorem packed_lane (m : Memory w) (n k : ℕ) (small : k<8) (wide : 3<w)
    (room : 8*n+k<2^w) :
    (Expr.op .mask .row (.lit 7) |>.eval m ((8*n+k : ℕ) : Word w)).val = k := by
  have seven : 7<2^w := (show 7 < 2^3 by decide).trans_le (Nat.pow_le_pow_right (n:=2) (by decide) wide.le)
  have mask : (8*n+k) &&& 7 = k :=
    (Nat.and_two_pow_sub_one_eq_mod (8*n+k) 3).trans (by change (8*n+k)%8=k; omega)
  simp only [Expr.eval,RowOp.opcode,BinaryOp.eval,Fin.val_cast_of_lt room,Fin.val_cast_of_lt seven,mask]
  exact Nat.mod_eq_of_lt (by omega)

theorem packed_eval (owners : Bank) (fields : Fin 7 → Expr) (m : Memory w) {n : ℕ} (i : Fin n) (j : Fin 7)
    (wide : 3<w) (room : 8*i.val+j.val<2^w) (dir : Owners owners n m) :
    (packed owners fields).eval m ((8*i.val+j.val : ℕ) : Word w) = (fields j).eval m (i.val:Word w) := by
  have lane := packed_lane m i.val j.val (by have := j.isLt; omega) wide room
  have row := dir i (j.castLE (by decide : 7≤8))
  have seven : 7 ≤ 2^w := (show 7 ≤ 2^3 by decide).trans (Nat.pow_le_pow_right (n:=2) (by decide) wide.le)
  rw [packed,eval_chooseField _ _ _ _ _ _ j (by omega) (by simpa using lane),eval_atRow]
  exact congrArg ((fields j).eval m) row

theorem packed_padding (owners : Bank) (fields : Fin 7 → Expr) (m : Memory w) (i : ℕ)
    (wide : 3<w) (room : 8*i+7<2^w) :
    (packed owners fields).eval m ((8*i+7 : ℕ) : Word w) = 0 := by
  have lane := packed_lane m i 7 (by decide) wide room
  rw [packed]
  have seven : 7 ≤ 2^w := (show 7 ≤ 2^3 by decide).trans (Nat.pow_le_pow_right (n:=2) (by decide) wide.le)
  exact eval_chooseField_outside _ _ _ _ _ _ (by omega) (by omega)

/-- All seven fields are written by one deterministic native instruction table.
The number of executions of the row body depends only on the fixed board size. -/
def report (out n : ℕ) (owners : Bank) (fields : Fin 7 → Expr) : Pass := ⟨out,8*n,packed owners fields⟩

theorem report_read (out n : ℕ) (owners : Bank) (fields : Fin 7 → Expr) (m : Memory w)
    (i : Fin n) (j : Fin 7) (wide : 3<w) (room : out+8*n < 2^w) (dir : Owners owners n m) :
    ((report out n owners fields).apply m) (out+8*i.val+j.val) = (fields j).eval m (i.val:Word w) := by
  have hi := i.isLt
  have hj := j.isLt
  let offset : Fin (8*n):=⟨8*i.val+j.val,by omega⟩
  have loaded:=ProtocolRAMGeneratedWrite.read_image out (8*n) (packed owners fields) m offset
  change image out (8*n) (packed owners fields) m (out+8*i.val+j.val)=_
  rw [show out+8*i.val+j.val=out+offset.val from Nat.add_assoc ..,loaded]
  exact packed_eval owners fields m i j wide (by omega) dir


end Hierarchy.ProtocolRAM

end OAI
