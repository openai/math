import OAI.Hierarchy.TaggedWireRolePageCore
import OAI.Hierarchy.TaggedWirePublicCount
import OAI.Hierarchy.ProbePositiveSiteRows

namespace OAI
/-! # Reading the local incident role as a single native word -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open AdaptiveProbe ReportSockets ProtocolRAM TaggedShorterSupergroups
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
set_option synthInstance.maxSize 512
variable {h W k attempts w H : ℕ} (S : PurchaseSampler)

def code (p : Public S h W k attempts) : ℕ :=
  (Fintype.equivFin (Incident.Fiber (site S) (site S p)) ⟨p,rfl⟩).val

set_option maxHeartbeats 1600000 in
theorem code_bound (p : Public S h W k attempts) :
    code S p<Incident.room k S.degree attempts+(1+2*k)+1 :=
  Nat.lt_of_lt_of_le (Fintype.equivFin (Incident.Fiber (site S) (site S p)) ⟨p,rfl⟩).isLt
    (site_card (h:=h) (W:=W) (k:=k) (attempts:=attempts) S (site S p))

theorem code_unique (v : Site h (2^W) k) (a b : Incident.Fiber (site S (attempts:=attempts)) v) :
    code S a.val=code S b.val ↔ a=b := by
  have rank {v' : Site h (2^W) k} (p : Incident.Fiber (site S (attempts:=attempts)) v') :
      code S p.val=(Fintype.equivFin (Incident.Fiber (site S (attempts:=attempts)) v') p).val := by
    rcases p with ⟨p,rfl⟩
    rfl
  rw [rank a,rank b]
  exact ⟨fun same=>(Fintype.equivFin _).injective (Fin.ext same),fun same=>by rw [same]⟩

namespace RoleROM
variable {S}
def publicTable (S : PurchaseSampler) (h W k attempts : ℕ) :=
  code S ∘ (Fintype.equivFin (Public S h W k attempts)).symm

theorem public_read {base : ℕ} {m : Memory w} (S : PurchaseSampler) (p : Public S h W k attempts)
    (ready : Mounted base (publicTable S h W k attempts) m) (input : Expr) (row : Word w)
    (room : Fintype.card (Public S h W k attempts)≤2^w) (seen : input.eval m row=
      ((Fintype.equivFin (Public S h W k attempts) p).val:Word w)) :
    (expr base (Fintype.card (Public S h W k attempts)) input).eval m row=(code S p:Word w) := by
  simpa only [publicTable,Function.comp_apply,Equiv.symm_apply_apply] using read ready input row _ room seen

/-- The positive hardware offers the packed supergroup and slot directly.
The table is indexed by those physical fields, independent of the matching. -/
def positiveTable (S : PurchaseSampler) (dir : Directory (reserved h W (copies k attempts)) H)
    (i : Fin (dir.groups*H)) : ℕ :=
  let q := finProdFinEquiv.symm i
  if h:∃x,packed dir x=q then code S (.inl (.inr h.choose)) else 0

theorem positive_at (S : PurchaseSampler) (dir : Directory (reserved h W (copies k attempts)) H)
    (x : StageColumns h (2^W)×Role k attempts) :
    positiveTable S dir (finProdFinEquiv (packed dir x))=code S (.inl (.inr x)) := by
  have hit : ∃y,packed dir y=packed dir x := ⟨x,rfl⟩
  simp only [positiveTable,Equiv.symm_apply_apply,dite_eq_left hit,(packed dir).injective hit.choose_spec]

theorem positive_read {base off : ℕ} {m : Memory w} (S : PurchaseSampler)
    (dir : Directory (reserved h W (copies k attempts)) H)
    (ready : Mounted base (positiveTable S dir) m) (offsets : SiteROM.Resident dir off m)
    (g s : Expr) (row : Word w) (x : StageColumns h (2^W)×Role k attempts)
    (room : dir.groups*H≤2^w) (groups : dir.groups≤2^w)
    (gAt : g.eval m row=((packed dir x).1.val:Word w)) (sAt : s.eval m row=((packed dir x).2.val:Word w)) :
    (expr base (dir.groups*H) (positiveKey off dir.groups g s)).eval m row = (code S (.inl (.inr x)):Word w) := by
  let y:=packed dir x
  have lookup : (SiteROM.offsets off dir.groups).read m (y.1.val:Word w)=((y.1.val*H:ℕ):Word w) := by
    rw [Bank.read,Fin.val_cast_of_lt (y.1.isLt.trans_le groups)]
    change m (off+y.1.val%ProtocolRAMPurchaseSampler.span dir.groups)=_
    rw [Nat.mod_eq_of_lt (y.1.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _))]
    exact offsets.offset y.1
  have address : (positiveKey off dir.groups g s).eval m row=((finProdFinEquiv y).val:Word w) := by
    simp only [positiveKey,Expr.eval,RowOp.opcode,BinaryOp.eval,gAt,sAt]
    change (SiteROM.offsets off dir.groups).read m (y.1.val:Word w)+(y.2.val:Word w)=_
    rw [lookup,←Nat.cast_add]
    apply congrArg (fun a:ℕ=>(a:Word w))
    change y.1.val*H+y.2.val=y.2.val+H*y.1.val
    ac_rfl
  rw [read ready _ _ _ room address,positive_at]

end RoleROM

namespace RoleProgram
def publicSites (h W k attempts : ℕ) (S : PurchaseSampler) (i : Fin (Fintype.card (Public S h W k attempts))) :=
  (name (site S ((Fintype.equivFin _).symm i))).val

end RoleProgram
end Hierarchy.ProbeStage.CoreBoard.HistoryRoles

end
end OAI
