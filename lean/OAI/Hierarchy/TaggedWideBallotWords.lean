import OAI.Hierarchy.TaggedWideBallotShape
import OAI.Hierarchy.TaggedWireRolePageCore
import OAI.Hierarchy.ProtocolRAMRowChoice

namespace OAI
/-! # Physical words of an elected party in the stored candidate ballot -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU.Ballot
open Computability.VPVNP.BurstRAM PrivateRAM
open ProbeStage.CoreBoard.HistoryRoles
open scoped Classical Fin.CommRing
variable {w n q L : ℕ}

/-- The committed packet code is zero off the elected set, and is one
plus the original finite menu ordinal on the elected set. -/
def code (start n : ℕ) : Expr := RoleROM.expr start n .row

theorem code_read (start : ℕ) (m : Memory w) (i : Fin n) (fit : n≤2^w) :
    (code start n).eval m (i.val:Word w)=m (start+i.val) := by
  change m (start+(i.val:Word w).val%ProtocolRAMPurchaseSampler.span n)=_
  rw [Fin.val_cast_of_lt (i.isLt.trans_le fit),Nat.mod_eq_of_lt (i.isLt.trans (ProtocolRAMPurchaseSampler.lt_span n))]

/-- Only a fixed finite number of public comparisons and literal local tags is needed. -/
def participant (atoms : ℕ) (menu : Expr) (party : Fin L) : Expr :=
  chooseField atoms 1 (fun i=>.lit (i.val*L+party.val+1)) menu

theorem participant_read (atoms : ℕ) (menu : Expr) (party : Fin L) (m : Memory w) (row : Word w)
    (atom : Fin atoms) (fit : 1+atoms≤2^w) (read : (menu.eval m row).val=atom.val+1) :
    (participant atoms menu party).eval m row=((atom.val*L+party.val+1:ℕ):Word w) := by
  exact eval_chooseField atoms 1 _ menu m row atom fit (by omega)

def field (atoms : ℕ) (menu : Expr) (counter : Fin q→Expr) (party : Fin L) : Fin (q+2)→Expr :=
  Fin.cases (participant atoms menu party) (Fin.cases (.op .add .row (.lit 1)) counter)

def fields (atoms : ℕ) (menu : Expr) (counter : Fin q→Expr) (site : Fin L→Expr) :
    Fields ⟨n,L,q+2⟩ := ⟨fun _=>menu,site,field atoms menu counter⟩

theorem field_candidate (atoms : ℕ) (menu : Expr) (counter : Fin q→Expr) (p : Fin L)
    (m : Memory w) (i : Fin n) :
    (field atoms menu counter p (0:Fin (q+1)).succ).eval m (i.val:Word w)=((i.val+1:ℕ):Word w) := by
  change (i.val:Word w)+1=_
  simp only [Nat.cast_add,Nat.cast_one]

theorem field_counter (atoms : ℕ) (menu : Expr) (counter : Fin q→Expr) (p : Fin L)
    (m : Memory w) (i : Fin n) (j : Fin q) :
    (field atoms menu counter p j.succ.succ).eval m (i.val:Word w)=(counter j).eval m (i.val:Word w) := rfl

theorem participant_index (atoms : ℕ) (menu : Expr) (party : Fin L) (m : Memory w) (row : Word w)
    (atom : Fin atoms) (menuFit : 1+atoms≤2^w) (tagsFit : atoms*L+1≤2^w)
    (read : (menu.eval m row).val=atom.val+1) :
    ((participant atoms menu party).eval m row).val=(finProdFinEquiv (atom,party)).val+1 := by
  rw [participant_read atoms menu party m row atom menuFit read]
  have bound := (finProdFinEquiv (atom,party)).isLt
  change party.val+L*atom.val<atoms*L at bound
  change _=party.val+L*atom.val+1
  rw [Fin.val_cast_of_lt (by rw [Nat.mul_comm atom.val L]; omega),Nat.mul_comm atom.val L,Nat.add_comm (L*atom.val) party.val]

end Hierarchy.ProtocolRAM.Calendar.WideCPU.Ballot
end

end OAI
