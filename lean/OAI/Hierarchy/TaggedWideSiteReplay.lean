import OAI.Hierarchy.TaggedWideSiteScatter
import OAI.Hierarchy.ProtocolRAMRowChoice
import OAI.Hierarchy.TaggedWireRolePageCore

namespace OAI
/-! # Native forward-lookup compilation for every local party and finite field -/

noncomputable section
namespace Hierarchy.ProtocolRAM.SiteScatter
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open ProbeStage.CoreBoard.HistoryRoles
open scoped Classical Fin.CommRing

variable {W I L C : ℕ}

def order (I L C : ℕ) : Fin I×(Fin L×Fin C) ≃ Fin (I*(L*C)) :=
  ((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv

/-- Three pages, each with one fixed word per (candidate, local party,
reported field). All address arithmetic and advice are public. -/
def directory (I L C : ℕ) (j : Fin 3) (r : Fin (I*(L*C))) : ℕ :=
  let q := (order I L C).symm r
  Fin.cases q.1.val (fun t=>Fin.cases q.2.1.val (fun _=>q.2.2.val) t) j

def column (base I L C : ℕ) (j : Fin 3) := RoleROM.expr (base+j.val*(I*(L*C))) (I*(L*C)) .row

def localTag (base : ℕ) (site : Fin L → Expr) : Expr :=
  chooseField L 0 (fun i=>(site i).atRow (column base I L C 0)) (column base I L C 1)

def fieldValue (base : ℕ) (field : Fin L → Fin C → Expr) : Expr :=
  chooseField L 0 (fun i=>chooseField C 0 (fun j=>(field i j).atRow (column base I L C 0))
    (column base I L C 2)) (column base I L C 1)

def selectedValue (base : ℕ) (siteLive : Fin L → Expr) (field : Fin L → Fin C → Expr) : Expr :=
  .branch .eq (localTag (I:=I) (C:=C) base siteLive) (.lit 0) (.lit 0) (fieldValue (I:=I) base field)

def fieldIndex (base : ℕ) (stride : Bank) (site : Fin L → Expr) : Expr :=
  RoleWidths.offset stride (localTag (I:=I) (C:=C) base site) (column base I L C 2)

variable {base : ℕ} (m : Memory W)
    (mounted : ∀j : Fin 3,RoleROM.Mounted (base+j.val*(I*(L*C))) (directory I L C j) m)
    (fit : I*(L*C)≤2^W) (partyFit : L≤2^W) (colFit : C≤2^W)

include mounted fit

theorem col_read (j : Fin 3) (q : Fin I×(Fin L×Fin C)) :
    (column base I L C j).eval m (((order I L C q).val):Word W)=
      (Fin.cases q.1.val (fun t=>Fin.cases q.2.1.val (fun _=>q.2.2.val) t) j:ℕ) := by
  simpa only [column,directory,Equiv.symm_apply_apply] using
    RoleROM.read (mounted j) (.row) (((order I L C q).val):Word W) (order I L C q) fit rfl

include partyFit

theorem tag_read (site : Fin L → Expr) (q : Fin I×(Fin L×Fin C)) :
    (localTag (I:=I) (C:=C) base site).eval m (((order I L C q).val):Word W)=
      (site q.2.1).eval m (q.1.val:Word W) := by
  rw [localTag,eval_chooseField _ _ _ _ _ _ q.2.1 (by omega),eval_atRow,col_read m mounted fit 0 q]
  · rfl
  · rw [col_read m mounted fit 1 q,Nat.zero_add]
    exact Fin.val_cast_of_lt (q.2.1.isLt.trans_le partyFit)

include colFit

theorem field_read (field : Fin L → Fin C → Expr) (q : Fin I×(Fin L×Fin C)) :
    (fieldValue (I:=I) base field).eval m (((order I L C q).val):Word W)=
      (field q.2.1 q.2.2).eval m (q.1.val:Word W) := by
  rw [fieldValue,eval_chooseField _ _ _ _ _ _ q.2.1 (by omega),eval_chooseField _ _ _ _ _ _ q.2.2 (by omega),
    eval_atRow,col_read m mounted fit 0 q]
  · rfl
  · rw [col_read m mounted fit 2 q,Nat.zero_add]
    exact Fin.val_cast_of_lt (q.2.2.isLt.trans_le colFit)
  · rw [col_read m mounted fit 1 q,Nat.zero_add]
    exact Fin.val_cast_of_lt (q.2.1.isLt.trans_le partyFit)

theorem value_read (live : Fin L → Expr) (field : Fin L → Fin C → Expr) (q : Fin I×(Fin L×Fin C)) :
    (selectedValue (I:=I) base live field).eval m (((order I L C q).val):Word W)=
      if (live q.2.1).eval m (q.1.val:Word W)=0 then 0 else (field q.2.1 q.2.2).eval m (q.1.val:Word W) := by
  simp only [selectedValue,Expr.eval,tag_read m mounted fit partyFit,field_read m mounted fit partyFit colFit,Comparison.test];
    split_ifs <;> simp_all

end Hierarchy.ProtocolRAM.SiteScatter

end
end OAI
