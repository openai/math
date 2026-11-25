import OAI.Hierarchy.TaggedWireRoleTableROM
import OAI.Hierarchy.TaggedWireRoleProgramCore

namespace OAI
/-! # Native endpoint role banks for initial and terminal turns -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open AdaptiveProbe ReportSockets ProtocolRAM TaggedShorterSupergroups
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
variable {w h W k attempts H : ℕ} (S : PurchaseSampler)

def labelled (out : Bool) (p : Public S h W k attempts) := 2*code S p+out.toNat

theorem labelled_unique {v : Site h (2^W) k} (a b : Incident.Fiber (site S (attempts:=attempts)) v) (x y : Bool) :
    labelled S x a.val=labelled S y b.val ↔ x=y ∧ a=b := by
  constructor
  · intro eq
    have val : 2*code S a.val+x.toNat=2*code S b.val+y.toNat := eq
    cases x <;> cases y <;> simp only [Bool.toNat_false,Bool.toNat_true] at val <;>
      first | exact ⟨rfl,(code_unique S _ _ _).mp (by omega)⟩ | omega
  · rintro ⟨rfl,rfl⟩;rfl

variable (L : Chart) (v : Socket) (mem : Memory w) (row : Word w)

def Resolved (p : Public S h W k attempts) : Prop :=
  (socketSite L v).eval mem row=((name (site S p)).val:Word w) ∧ (socketCode L v).eval mem row=(code S p:Word w)

theorem public_resolved (p : Public S h W k attempts) (kind : v.positive.eval mem row=0)
    (count : L.publicCount=Fintype.card (Public S h W k attempts)) (room : L.publicCount≤2^w)
    (sites : RoleROM.Mounted (L.publicBase+L.publicCount) (publicSites h W k attempts S) mem)
    (codes : RoleROM.Mounted L.publicBase (RoleROM.publicTable S h W k attempts) mem)
    (idx : v.ordinal.eval mem row=((Fintype.equivFin (Public S h W k attempts) p).val:Word w)) :
    Resolved S L v mem row p := by
  have actualRoom : Fintype.card (Public S h W k attempts)≤2^w := count ▸ room
  have si:=RoleROM.read sites v.ordinal row _ actualRoom idx
  have co:=RoleROM.public_read S p codes v.ordinal row actualRoom idx
  have off (yes no : Expr) : (choose v yes no).eval mem row=no.eval mem row := by
    simp [choose,Expr.eval,Comparison.test,kind]
  change (socketSite L v).eval mem row=_ ∧ (socketCode L v).eval mem row=_
  rw [socketSite,socketCode,off,off]
  constructor
  · simpa only [count,publicSites,Equiv.symm_apply_apply] using si
  · simpa only [count] using co


theorem positive_resolved (dir : Directory (reserved h W (copies k attempts)) H)
    (x : StageColumns h (2^W)×Role k attempts) (kind : v.positive.eval mem row≠0)
    (gs : L.groups=dir.groups) (ss : L.slots=H)
    (sites : SiteROM.Resident dir L.offBase mem) (codes : RoleROM.Mounted L.roleBase (RoleROM.positiveTable S dir) mem)
    (room : dir.groups*H≤2^w) (fit : dir.groups≤2^w)
    (groupAt : v.group.eval mem row=((packed dir x).1.val:Word w)) (slotAt : v.slot.eval mem row=((packed dir x).2.val:Word w)) :
    Resolved S L v mem row (.inl (.inr x)) := by
  have si:=sites.read v.group v.slot row (packed dir x).1 (packed dir x).2 fit room groupAt slotAt
  have co:=RoleROM.positive_read S dir codes sites v.group v.slot row x room fit groupAt slotAt
  have on (yes no : Expr) : (choose v yes no).eval mem row=yes.eval mem row := by
    simp [choose,Expr.eval,Comparison.test,kind]
  change (socketSite L v).eval mem row=_ ∧ (socketCode L v).eval mem row=_
  rw [socketSite,socketCode,on,on,gs,ss]
  exact ⟨by simpa [SiteROM.code,publicSite_packed,site,paidSite] using si,co⟩

def actual (out : Bool) {w : ℕ} (v : Bool→Public S h W k attempts) (right : Bool) (siteId : Bool) : Word w :=
  let a := (name (site S (v false))).val
  let b := (name (site S (v true))).val
  let p := v (if a<b then right else !right)
  if siteId then ((name (site S p)).val:Word w) else (labelled S out p:Word w)

theorem fields (v : Bool→Socket) (p : Bool→Public S h W k attempts) (out : Bool)
    (observed : ∀b,Resolved S L (v b) mem row (p b)) (fit : siteLast h (2^W) k+1≤2^w) :
    (field L v out 0).eval mem row=actual S out p false true ∧
    (field L v out 1).eval mem row=actual S out p true true ∧
    (field L v out 2).eval mem row=actual S out p false false ∧
    (field L v out 3).eval mem row=actual S out p true false := by
  have ab : (((name (site S (p false))).val:Word w)<((name (site S (p true))).val:Word w)) ↔
      name (site S (p false))<name (site S (p true)) := by
    rw [Fin.lt_def,Fin.val_cast_of_lt ((name (site S (p false))).isLt.trans_le fit),
      Fin.val_cast_of_lt ((name (site S (p true))).isLt.trans_le fit)]
    rfl
  by_cases order:name (site S (p false))<name (site S (p true)) <;>
    simp [field,sortedRead,tagged,Expr.eval,Comparison.test,RowOp.opcode,BinaryOp.eval,(observed false).1,
      (observed true).1,(observed false).2,(observed true).2,ab,order,actual,labelled,two_mul]

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram

end
end OAI
