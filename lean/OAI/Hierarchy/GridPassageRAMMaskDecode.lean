import OAI.Hierarchy.GridPassageRAMDecode
import OAI.Hierarchy.GridPassageRAMMask
import OAI.Hierarchy.GridPassageRAMPadIndex

namespace OAI
/-! # Physical mark correction at a padded rank -/

namespace Hierarchy.GridPassageRAMMask

open Computability.VPVNP.BurstRAM PrivateRAM GridPassageRAMPadIndex
open GridPassageRAMRow (address_val divWord_cast modWord_cast)
open scoped Fin.CommRing

variable {w k g B : ℕ}

/-- Exact values of the pages read by the finalizer. A chosen rail is required
only when the native test actually clears its mark. -/
structure MaskReads (m : Memory w) (C O compact powers width count e : ℕ)
    (x : Fin k → Fin g) (j : Fin k) (r : Fin B) : Prop where
  widthVal : m (compact+6+j.val) = (width : Word w)
  countVal : m (C+key x j) = (count : Word w)
  power : m (powers+j.val) = ((g^j.val : ℕ) : Word w)
  chosen : width≤r.val ∧ r.val<count → m (O+ordinal x j r) = (e : Word w)

structure MaskRoom (w C O compact powers M width count e : ℕ)
    (x : Fin k → Fin g) (j : Fin k) (r : Fin B) : Prop where
  capacity : B < 2^w
  axes : k < 2^w
  radix : g < 2^w
  extent : g^k < 2^w
  ordinal : GridPassageRAMPadIndex.ordinal x j r < 2^w
  widthFit : width < 2^w
  countFit : count < 2^w
  widthAddr : compact+6+j.val < 2^w
  countAddr : C+key x j < 2^w
  powerAddr : powers+j.val < 2^w
  chosenAddr : width≤r.val ∧ r.val<count → O+GridPassageRAMPadIndex.ordinal x j r < 2^w
  markAddr : width≤r.val ∧ r.val<count → M+e*g+(x j).val < 2^w

/-- The padded row clears the selected rail's mark exactly in the interval
between the direction width and stored count. The unused choice entries need
no initialization. -/
theorem maskDecode (limit C O compact powers M width count e : ℕ)
    (x : Fin k → Fin g) (j : Fin k) (r : Fin B) (m : Memory w)
    (reads : MaskReads m C O compact powers width count e x j r)
    (room : MaskRoom w C O compact powers M width count e x j r) :
    wordStep (values w limit B k g C O compact powers M) (ordinal x j r : Word w) m =
      if width≤r.val ∧ r.val<count then Function.update m (M+e*g+(x j).val) 0 else m := by
  let v := values w limit B k g C O compact powers M
  let i := ordinal x j r
  let b := key x j
  let a := (finFunctionFinEquiv x).val
  let s := g^j.val
  have BAt : v 1 = (B : Word w) := rfl
  have kAt : v 2 = (k : Word w) := rfl
  have gAt : v 3 = (g : Word w) := rfl
  have CAt : v 4 = (C : Word w) := rfl
  have OAt : v 5 = (O : Word w) := rfl
  have widthsAt : v 6 = ((compact+6 : ℕ) : Word w) := by
    change (compact : Word w)+6 = ((compact+6 : ℕ) : Word w)
    simp only [Nat.cast_add,Nat.cast_ofNat]
  have powersAt : v 7 = (powers : Word w) := rfl
  have marksAt : v 8 = (M : Word w) := rfl
  have bf : b < 2^w := by
    change key x j < 2^w
    rw [← div_slot x j r]
    exact (Nat.div_le_self ..).trans_lt room.ordinal
  have af : a < 2^w := (finFunctionFinEquiv x).isLt.trans room.extent
  have sf : s < 2^w :=
    (Nat.pow_le_pow_right (Nat.zero_lt_of_lt (x j).isLt) j.isLt.le).trans_lt room.extent
  have getKey : BinaryOp.div.eval (i : Word w) (B : Word w) = (b : Word w) :=
    (divWord_cast i B room.ordinal room.capacity).trans (congrArg (fun z : ℕ => (z : Word w)) (div_slot x j r))
  have getRank : BinaryOp.mod.eval (i : Word w) (B : Word w) = (r.val : Word w) :=
    (modWord_cast i B room.ordinal room.capacity).trans (congrArg (fun z : ℕ => (z : Word w)) (mod_slot x j r))
  have getCell : BinaryOp.div.eval (b : Word w) (k : Word w) = (a : Word w) :=
    (divWord_cast b k bf room.axes).trans (congrArg (fun z : ℕ => (z : Word w)) (div_axis x j))
  have getDir : BinaryOp.mod.eval (b : Word w) (k : Word w) = (j.val : Word w) :=
    (modWord_cast b k bf room.axes).trans (congrArg (fun z : ℕ => (z : Word w)) (mod_axis x j))
  have widthRead : m (((compact+6 : ℕ) : Word w)+(j.val : Word w)).val = (width : Word w) := by
    rw [address_val _ _ room.widthAddr]
    exact reads.widthVal
  have countRead : m ((C : Word w)+(b : Word w)).val = (count : Word w) := by
    rw [address_val _ _ room.countAddr]
    exact reads.countVal
  have headEq : header v (i : Word w) m =
      ⟨(r.val : Word w),(a : Word w),(j.val : Word w),(width : Word w),(count : Word w)⟩ := by
    simp only [header,BAt,kAt,CAt,widthsAt,getKey,getRank,getCell,getDir,
      widthRead,countRead]
  apply wordStep_natStep v (i : Word w) m r.val width count (M+e*g+(x j).val)
  · rw [headEq]
    exact Fin.val_cast_of_lt (r.isLt.trans room.capacity)
  · rw [headEq]
    exact Fin.val_cast_of_lt room.widthFit
  · rw [headEq]
    exact Fin.val_cast_of_lt room.countFit
  · intro gate
    have physical : m ((O : Word w)+(i : Word w)).val = (e : Word w) := by
      rw [address_val _ _ (room.chosenAddr gate)]
      exact reads.chosen gate
    have step : m ((powers : Word w)+(j.val : Word w)).val = (s : Word w) := by
      rw [address_val _ _ room.powerAddr]
      exact reads.power
    have getCoord : BinaryOp.mod.eval ((a/s : ℕ) : Word w) (g : Word w) = ((x j).val : Word w) :=
      (modWord_cast (a/s) g ((Nat.div_le_self ..).trans_lt af) room.radix).trans
        (congrArg (fun z : ℕ => (z : Word w)) (coordinate x j))
    have dst : (M : Word w) + ((e : Word w)*(g : Word w)+((x j).val : Word w)) =
        ((M+e*g+(x j).val : ℕ) : Word w) := by push_cast; ac_rfl
    simp only [address,headEq,OAt,powersAt,marksAt,gAt,physical,step,divWord_cast a s af sf,
      getCoord,dst,Fin.val_cast_of_lt (room.markAddr gate)]

end Hierarchy.GridPassageRAMMask

end OAI
