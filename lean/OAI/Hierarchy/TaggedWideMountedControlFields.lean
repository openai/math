import OAI.Hierarchy.TaggedWideControlOperands
import OAI.Hierarchy.TaggedWideBallotShape
import OAI.Hierarchy.TaggedWireRolePageCore
import OAI.Hierarchy.ProtocolRAMHistogram

namespace OAI
/-! # Flatten the two true dated role pages into the fixed gate control page -/
noncomputable section
namespace Hierarchy.ProtocolRAM.SiteControls
open Computability.VPVNP.BurstRAM PrivateRAM Calendar.WideCPU ProbeStage.CoreBoard.HistoryRoles
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing Classical BigOperators

def fieldCount (D : ℕ) := Fintype.card (Field D)
def fieldNumber (D : ℕ) : Field D ≃ Fin (fieldCount D) := Fintype.equivFin _

/-- The two measured arrays of the authentic finite selected packet report hold
released and installed leading widths at the old and new opposite site, respectively.
A feed has no corresponding ballot rows and hence reserves no ballot cells. -/
def lowFieldFrom {D : ℕ} (first sites ballotStart fields : ℕ) (side : Bool) (i : Fin D) : Expr :=
  if fields=0 then .lit 0 else
    let offset:=first+side.toNat*D+i.val
    .lookup (RoleROM.bank ballotStart (sites*fields))
      (.op .add (scale fields .row) (.lit offset))

def lowField {D : ℕ} (sites ballotStart fields : ℕ) :=
  lowFieldFrom (D:=D) (fields-(D+D)) sites ballotStart fields

def fixed (sites n D cap : ℕ) (table : Bank) (old new ballot fields : ℕ) (lowStart : ℕ := fields-(D+D)) :
    Fields (⟨sites,1,fieldCount D⟩ : Shape) where
  selected := fun _=>.lit 1
  site := fun _=>.row
  value := fun _ f=>
    let src := fun b : Bool=>columns (D:=D) n (if b then new else old) sites
      (ProtocolRAMPurchaseSampler.bits (sites*D)) table .row
    compile cap src (lowFieldFrom lowStart sites ballot fields) ((fieldNumber D).symm f)

theorem low_at_from {D W sites : ℕ} (base fields first : ℕ) (side : Bool) (q : Fin D) (i : Fin sites)
    (m : Memory W) (sized : first+(D+D)≤fields) (room : sites*fields≤2^W) :
    (lowFieldFrom first sites base fields side q).eval m (i.val:Word W)=
     m (base+(i.val*fields+(first+side.toNat*D+q.val))) := by
  have nd : 0<D := Nat.zero_lt_of_lt q.isLt
  have nf : fields≠0 := by omega
  let k:=first+side.toNat*D+q.val
  have bound : k<fields := by
    cases side <;> simp only [k,Bool.toNat_false,Bool.toNat_true,Nat.zero_mul,Nat.one_mul,Nat.add_zero] <;>
      have:=q.isLt <;> omega
  have eqn : (finProdFinEquiv (i,(⟨k,bound⟩:Fin fields))).val=i.val*fields+k := by
    simp [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  have top : i.val*fields+k<sites*fields := eqn ▸ (finProdFinEquiv (i,(⟨k,bound⟩:Fin fields))).isLt
  change (lowFieldFrom first sites base fields side q).eval m (i.val:Word W)=m (base+(i.val*fields+k))
  rw [lowFieldFrom,ite_eq_right nf]
  change m (base+((_ : Expr).eval m (i.val:Word W)).val%(RoleROM.bank base (sites*fields)).size)=_
  have word : (Expr.op .add (scale fields .row) (.lit k)).eval m (i.val:Word W)=
      ((i.val*fields+k:ℕ):Word W) := by simp [Expr.eval,RowOp.opcode,BinaryOp.eval,Nat.cast_add,Nat.cast_mul,mul_comm]
  have bankFits : i.val*fields+k < (RoleROM.bank base (sites*fields)).size :=
    top.trans (ProtocolRAMPurchaseSampler.lt_span _)
  rw [word,Fin.val_cast_of_lt (top.trans_le room),Nat.mod_eq_of_lt bankFits]

theorem low_at {D W sites : ℕ} (base fields : ℕ) (side : Bool) (q : Fin D) (i : Fin sites)
    (m : Memory W) (sized : D+D≤fields) (room : sites*fields≤2^W) :
    (lowField sites base fields side q).eval m (i.val:Word W)=
     m (base+(i.val*fields+(fields-(D+D)+side.toNat*D+q.val))) :=
  low_at_from base fields (fields-(D+D)) side q i m (by omega) room

end Hierarchy.ProtocolRAM.SiteControls

end
end OAI
