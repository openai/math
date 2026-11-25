import OAI.Hierarchy.TaggedWireOriginalSocketExpr
import OAI.Hierarchy.TaggedWireOriginalTableData
import OAI.Hierarchy.TaggedWireRoleSemantics
import OAI.Hierarchy.ProtocolRAMCoreCatalogueSource
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueSupport

namespace OAI
/-! # Role operands from the actual core and acquired positive-socket columns -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open AdaptiveProbe ReportSockets ProtocolRAM Calendar TaggedShorterSupergroups
open ThreeFlat.RAM DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {w h W k attempts G K R H : ℕ} (S : PurchaseSampler)

def packedSocket (start K copies : ℕ) (kind global group port tag : Expr) : Socket :=
  ⟨kind,global,.lookup (ProtocolRAMSupergroupDirectory.groupBank start K) group,
    addressExpr copies 1 (ProtocolRAMSupergroupDirectory.offsetBank start K) group port tag⟩

theorem packed_resolved (L : Chart) (dir : Directory (reserved h W (copies k attempts)) H) (start : ℕ)
    (groups : Fin K≃AllGroups h (2^W)) (m : Memory w) (row : Word w) (kind global group port tag : Expr)
    (x : StageColumns h (2^W)×Role k attempts) (on : kind.eval m row≠0)
    (gs : L.groups=dir.groups) (ss : L.slots=H) (sites : SiteROM.Resident dir L.offBase m)
    (codes : RoleROM.Mounted L.roleBase (RoleROM.positiveTable S dir) m)
    (header : ∀g,let j:=((groups.symm g).val:Word w)
      (ProtocolRAMSupergroupDirectory.groupBank start K).read m j=((dir.group g).val:Word w) ∧
      (ProtocolRAMSupergroupDirectory.offsetBank start K).read m j=(dir.base g:Word w))
    (gf : dir.groups≤2^w) (sf : dir.groups*H≤2^w)
    (grp : group.eval m row=((groups.symm (owner x.1)).val:Word w))
    (inp : port.eval m row=((socketPort x.1).val:Word w))
    (role : tag.eval m row=((socketTag x.1 x.2).val:Word w)) :
    Resolved S L (packedSocket start K (copies k attempts) kind global group port tag) m row (.inl (.inr x)) := by
  apply positive_resolved S L _ m row dir x on gs ss sites codes sf gf
  · simp only [packedSocket,Expr.eval,grp];exact (header (owner x.1)).1
  · simp only [packedSocket,addressExpr,Expr.eval,RowOp.opcode,BinaryOp.eval,eval_scale,grp,inp,role,(header (owner x.1)).2]
    change _=(((dir.base (owner x.1)+(offset x.1 x.2).val):ℕ):Word w)
    rw [offset_val]
    push_cast
    ring

/-- The actual core CT group/input/output record and fixed layer tags. Static
free rows read a single original role ordinal in a separate public table. -/
def coreInputs (base freeBase R bits superStart K k attempts : ℕ) (b : Bool) : Socket :=
  let dir := if b then 1 else 0
  packedSocket superStart K (copies k attempts) (CoreCatalogue.field base R 0)
    (RoleROM.expr (freeBase+dir*R) R .row) (CoreCatalogue.globalGroup base R bits)
    (CoreCatalogue.pointed base R bits (if b then 5 else 4)) (CoreCatalogue.field base R (if b then 8 else 7))

/-- North and south genuinely read different selected ends of the same acquired
chain. The selected bits, owner group, port and role remain its original fields. -/
def boughtInputs (v : BoughtSockets.Directory attempts) (S : PurchaseSampler) (h W k depth K : ℕ) (side : Bool) : Socket :=
  let f:=v.fields S h W k depth side
  packedSocket v.superBase K (copies k attempts) (.lit 1) (.lit 0) f.group f.port f.tag

theorem free_resolved (L : Chart) (order : Fin R≃Edges S h (2^W) k)
    (base freeBase bits superStart K : ℕ) (m : Memory w) (i : Fin R) (f : Free S h (2^W) k) (side : Bool)
    (edge : order i=.inl f) (flag : (CoreCatalogue.field base R 0).eval m (i.val:Word w)=0)
    (card : L.publicCount=Fintype.card (Public S h W k attempts)) (room : L.publicCount≤2^w)
    (rFit : R≤2^w) (tables : RoleROM.Mounted (freeBase+side.toNat*R) (freeTable S order attempts side) m)
    (sites : RoleROM.Mounted (L.publicBase+L.publicCount) (publicSites h W k attempts S) m)
    (codes : RoleROM.Mounted L.publicBase (RoleROM.publicTable S h W k attempts) m) :
    Resolved (attempts:=attempts) S L (coreInputs base freeBase R bits superStart K k attempts side)
      m (i.val:Word w) (.inl (.inl (f,side))) := by
  apply public_resolved S L _ m _ _ flag card room sites codes
  have got:=RoleROM.read tables .row (i.val:Word w) i rFit rfl
  cases side <;> simpa [coreInputs,freeTable,edge,packedSocket] using got

theorem bought_resolved (L : Chart) (v : BoughtSockets.Directory attempts) (depth : ℕ)
    (dir : Directory (reserved h W (copies k attempts)) H) (groups : Fin K≃AllGroups h (2^W))
    (m : Memory w) (row : Word w) (x : StageColumns h (2^W)×Role k attempts) (side : Bool)
    (one : (1:Word w)≠0) (gs : L.groups=dir.groups) (ss : L.slots=H) (sites : SiteROM.Resident dir L.offBase m)
    (codes : RoleROM.Mounted L.roleBase (RoleROM.positiveTable S dir) m)
    (super : ∀g,let j:=((groups.symm g).val:Word w)
      (ProtocolRAMSupergroupDirectory.groupBank v.superBase K).read m j=((dir.group g).val:Word w) ∧
      (ProtocolRAMSupergroupDirectory.offsetBank v.superBase K).read m j=(dir.base g:Word w))
    (gf : dir.groups≤2^w) (sf : dir.groups*H≤2^w)
    (observed : BoughtSockets.Reads (v.fields S h W k depth side) m row groups x) :
    Resolved S L (boughtInputs v S h W k depth K side) m row (.inl (.inr x)) := by
  exact packed_resolved S L dir v.superBase groups m row _ _ _ _ _ x one gs ss sites codes super gf sf
    observed.group observed.port observed.tag

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram

end
end OAI
