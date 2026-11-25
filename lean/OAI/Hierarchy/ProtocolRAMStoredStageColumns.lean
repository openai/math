import OAI.Hierarchy.ProtocolRAMColumnDirectory
import OAI.Hierarchy.ProtocolRAMStripColumnInputs
import OAI.Hierarchy.ProtocolRAMCoreCatalogueOperands
import OAI.Hierarchy.ProbePositiveSiteRows

namespace OAI
/-! # Runtime conversion of a tile, side, and stage into a global column -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets.ColumnROM
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {w h W k attempts K H : ℕ}

def stageInputs (k attempts remap : ℕ) (t : StageAt h (2^W)) (s : Bool) (tile : Expr) : Inputs :=
  let ct := PurchaseCT.banks t
  ⟨.lookup (ReportGroupROM.bank remap h (2^W) t) (.lookup ct.group tile),
    .lookup (if s then ct.output else ct.input) tile,
    .lit ((Fintype.equivFin (Bool×Role k attempts)) (s,.inl none)).val⟩

def stageColumn (columnBase remap sitesBase superBase K G H k attempts : ℕ)
    (t : StageAt h (2^W)) (s : Bool) (tile : Expr) : Expr :=
  let x := stageInputs k attempts remap t s tile
  project columnBase h (2^W) k (SiteROM.atPort sitesBase G H superBase K (ReportSockets.copies k attempts)
    x.group x.port x.tag)

def chosenColumn (π : Equiv.Perm (Fin (2^h))) (t : StageAt h (2^W)) (p : Fin (2^h)) (s : Bool) :
    CoreBoard.Columns h (2^W) :=
  let scan := advisedStage h (2^W) π t
  if s then outputCol t (scan.group p) (scan.output p) else inputCol t (scan.group p) (scan.input p)

/-- The semantic record gathers the physically checked immutable banks shared
by every source, target, and intermediate position. -/
structure Tables (h W k attempts columnBase remap sitesBase superBase : ℕ)
    (groups : Fin K ≃ AllGroups h (2^W))
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (ReportSockets.copies k attempts)) H)
    (π : Equiv.Perm (Fin (2^h))) (m : Memory w) : Prop where
  columns : Resident columnBase h (2^W) k m
  sites : SiteROM.Resident dir sitesBase m
  names : ReportGroupROM.Resident remap groups PurchaseCT.groupNumber m
  geometry : Calendar.CoreCatalogue.Geometry π m (2^W)
  super : ∀g, let idx := ((groups.symm g).val:Word w)
    (ProtocolRAMSupergroupDirectory.groupBank superBase K).read m idx=((dir.group g).val:Word w) ∧
    (ProtocolRAMSupergroupDirectory.offsetBank superBase K).read m idx=(dir.base g:Word w)
  groupFit : dir.groups≤2^w
  siteFit : dir.groups*H≤2^w

theorem stage_read (columnBase remap sitesBase superBase : ℕ) (groups : Fin K ≃ AllGroups h (2^W))
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (ReportSockets.copies k attempts)) H)
    (π : Equiv.Perm (Fin (2^h))) (m : Memory w) (tables : Tables h W k attempts columnBase remap sitesBase superBase groups dir π m)
    (t : StageAt h (2^W)) (s : Bool) (tile : Expr) (row : Word w) (p : Fin (2^h))
    (actual : tile.eval m row=(p.val:Word w)) :
    (stageColumn columnBase remap sitesBase superBase K dir.groups H k attempts t s tile).eval m row=
      (number (chosenColumn π t p s):Word w) := by
  let a := advisedStage h (2^W) π t
  let socket : StageColumns h (2^W) := ⟨t,a.group p,if s then .inr (a.output p) else .inl (a.input p)⟩
  let x : StageColumns h (2^W)×Role k attempts := (socket,.inl none)
  let operands := stageInputs k attempts remap t s tile
  have group : operands.group.eval m row=((groups.symm (owner x.1)).val:Word w) := by
    change (ReportGroupROM.bank remap h (2^W) t).read m ((PurchaseCT.banks t).group.read m (tile.eval m row))=_
    rw [actual,(tables.geometry t).group p]
    exact tables.names t (a.group p)
  have port : operands.port.eval m row=((socketPort x.1).val:Word w) := by
    cases s <;> simp only [operands,stageInputs,Expr.eval,actual,Bool.false_eq_true,ite_false,ite_true]
    · exact (tables.geometry t).input p
    · exact (tables.geometry t).output p
  have role : operands.tag.eval m row=((socketTag x.1 x.2).val:Word w) := by cases s <;> rfl
  have actualSite := SiteROM.read_port dir sitesBase superBase groups m tables.sites tables.super x
    operands.group operands.port operands.tag row tables.groupFit tables.siteFit group port role
  have physical := project_read columnBase h (2^W) k _ (physicalSite x) m row tables.columns actualSite
  cases s <;> exact physical

inductive PayloadChoice (h W : ℕ) where
  | source
  | target
  | stage (t : StageAt h (2^W)) (s : Bool)

def payloadColumn (columnBase remap sitesBase superBase K G H k attempts : ℕ) : PayloadChoice h W → Expr
  | .source => .lookup (outer columnBase h (2^W) k false) .row
  | .target => .lookup (outer columnBase h (2^W) k true) (.lookup (Native.initialOutput h) .row)
  | .stage t s => stageColumn columnBase remap sitesBase superBase K G H k attempts t s .row

def payloadValue (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) : PayloadChoice h W → CoreBoard.Columns h (2^W)
  | .source => .inl p
  | .target => .inr (.inr (π p))
  | .stage t s => chosenColumn π t p s

theorem payload_read (columnBase remap sitesBase superBase : ℕ) (groups : Fin K ≃ AllGroups h (2^W))
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (ReportSockets.copies k attempts)) H)
    (π : Equiv.Perm (Fin (2^h))) (m : Memory w) (tables : Tables h W k attempts columnBase remap sitesBase superBase groups dir π m)
    (raw : Native.Resident (Native.initialOutput h) m (fun p : Fin (2^h)=>(π p).val))
    (p : Fin (2^h)) (choice : PayloadChoice h W) :
    (payloadColumn columnBase remap sitesBase superBase K dir.groups H k attempts choice).eval m (p.val:Word w)=
      (number (payloadValue π p choice):Word w) := by
  cases choice with
  | source => exact tables.columns.port false p
  | target => simp only [payloadColumn,Expr.eval,raw p];exact tables.columns.port true (π p)
  | stage t s => exact stage_read _ _ _ _ groups dir π m tables t s .row _ p rfl

end Hierarchy.ProtocolRAM.BoughtSockets.ColumnROM
end

end OAI
