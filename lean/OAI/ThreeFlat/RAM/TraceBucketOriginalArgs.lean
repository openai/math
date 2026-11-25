import OAI.ThreeFlat.RAM.TraceBucketOperands

namespace OAI
/-! # The thirteen numerical operands of one original trivalent cell -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open Diagonal.TraceSourceOwner
open scoped Fin.CommRing
variable {W : ℕ}

def originalInputs (s : Layout) (m : ℕ→ℕ) (lane row field : ℕ) : Fin 13 → ℕ :=
  let i := row-s.relays
  let slot := i%s.slots
  let site := lane*s.lowRows+i/s.slots
  let source := m (s.readAt site slot field)
  ![field,source,ownerAt s.shape 1 site source,site,s.slots,slot,s.lowRows,s.pinCount lane,s.tags,s.bank,
    2^(s.depth-1),s.dictionary,s.tableIds]

theorem origArgs_value (s : Layout) (v : Fin 4→Word W) (data : Fin 1→Word W) (m : Memory W) (cap : ℕ) :
    let i := (v 0).val-s.relays
    let a := (v 2).val*s.lowRows+i/s.slots
    let j := i%s.slots
    let n := (m (s.readAt a j (v 1).val)).val
    s.relays≤(v 0).val → s.slots<2^W → s.shape.header<2^W →
    s.pinLow (v 2).val+2*s.lowRows<2^W → s.readAt a j (v 1).val<2^W →
    (∀ l, TraceOwnerFormula.vars s.shape 1 n a l<2^cap) → 5*cap+128≤W →
    (∀ l, originalInputs s (fun q => (m q).val) (v 2).val (v 0).val (v 1).val l < 2^W) →
    operands (origArgs s) data m v = originalInputs s (fun q => (m q).val) (v 2).val (v 0).val (v 1).val := by
  intro i a j n after slots hdr extFit rawFit dim margin words
  let e : Term W 1 4 := Term.binary .sub (.result 0) (.literal s.relays)
  let sec : Term W 1 4 := Term.binary .mod e (.literal s.slots)
  let site : Term W 1 4 := Term.binary .add (laneBase s) (Term.binary .div e (.literal s.slots))
  let source := raw s site sec (.result 1)
  have indexFit : i<2^W := (Nat.sub_le _ _).trans_lt (v 0).isLt
  have he : e.eval data m v=(i : Word W) := by
    simpa [e,i,Term.eval,natOp] using PhysicalPinsExpr.op_cast (w:=W) .sub (v 0).val s.relays after
  have hj : sec.eval data m v=(j : Word W) := by
    simpa only [sec,Term.eval_binary,he,Term.eval_literal,j,natOp] using
      PhysicalPinsExpr.op_cast (w:=W) .mod i s.slots ⟨indexFit,slots⟩
  have ha : site.eval data m v=(a : Word W) := by
    simp only [site,Term.eval_binary,laneBase_value,he,Term.eval_literal,
      PhysicalPinsExpr.op_cast .div i s.slots ⟨indexFit,slots⟩,natOp,a]
    simp [BinaryOp.eval]
  have hn : source.eval data m v=(n : Word W) := by
    simpa [source,n] using raw_value s v data m site sec (.result 1) a j (v 1).val ha hj (by simp [Term.eval]) rawFit
  have ho := direct_owner s data m v source site n a cap hn ha dim margin
  have hx := ext_value s v data m hdr extFit
  funext t
  have hword : ((origArgs s t : Term W 1 4)).eval data m v =
      (originalInputs s (fun q => (m q).val) (v 2).val (v 0).val (v 1).val t : Word W) := by
    fin_cases t
    · exact (show (↑(v 1).val : Word W) = v 1 by simp).symm
    · exact hn
    · exact ho
    · exact ha
    · rfl
    · exact hj
    · rfl
    · exact hx
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  exact (congrArg Fin.val hword).trans (Fin.val_cast_of_lt (words t))

end ThreeFlat.RAM.TraceBucketAtom

end OAI
