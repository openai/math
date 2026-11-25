import OAI.Hierarchy.ProtocolRAMStripColumnInputs
import OAI.Hierarchy.ProtocolRAMBoughtEndpointWords
import OAI.Hierarchy.ProtocolRAMCatalogueRowFields
import OAI.Hierarchy.ProtocolRAMCalendarLiveCount

namespace OAI
/-! # Relative chronological candidate rows in the terminal geometry serializer -/

namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen ReportSockets ProbeStage.CoreBoard
open TaggedShorterSupergroups Calendar Calendar.CatalogueRows
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
noncomputable section
variable {z W k attempts K H w : ℕ}

def Directory.ofChart {q goods : ℕ} (outer keys remap super sites : ℕ) (order : Fin attempts→Attempt)
    (C : Chart w q goods) (shelf : Fin attempts→Shelf) : Directory attempts where
  outerBase:=outer
  keysBase:=keys
  remapBase:=remap
  superBase:=super
  sitesBase:=sites
  shelf:=shelf
  flagBase a:=(repair C (order a)).purchaseOut
  menuBase a:=(repair C (order a)).boughtFields 6

def Directory.fields (v : Directory attempts) (S : PurchaseSampler) (z W k depth : ℕ) (side : Bool) : Inputs :=
  let head:=v.header z (2^W) k S.degree depth
  let x:=fun a=>event v.remapBase v.keysBase (v.shelf a) S z (2^W) k depth a side
  ⟨select head (fun a=>(x a).group),select head (fun a=>(x a).port),select head (fun a=>(x a).tag)⟩

def Directory.archived (v : Directory attempts) (z d k D depth : ℕ) (base : Fin attempts→ℕ) : Expr :=
  let head:=v.header z d k D depth
  select head (fun a=>.lookup ⟨base a,ProtocolRAMPurchaseSampler.bits head.ports⟩ .row)

/-- Every expression is evaluated at the original padded bought-row ordinal.
Only multiplication by the fixed lane/role count occurs in the endpoint queries. -/
def Directory.source (v : Directory attempts) (S : PurchaseSampler) (z W k depth oldGroups bins width : ℕ) : BoughtSource :=
  let f:=v.fields S z W k depth
  let site:=fun side=>SiteROM.atPort v.sitesBase bins width v.superBase oldGroups (ReportSockets.copies k attempts)
    (f side).group (f side).port (f side).tag
  ⟨.lookup (ProtocolRAMSupergroupDirectory.groupBank v.superBase oldGroups) (f false).group,
    site false,site true,v.archived z (2^W) k S.degree depth v.flagBase,
    v.archived z (2^W) k S.degree depth v.menuBase⟩

theorem Directory.dispatch (v : Directory attempts) (z d k D depth : ℕ) (m : Memory w)
    (load : (v.header z d k D depth).Loaded m) (fit : attempts≤2^w)
    (a : Fin attempts) (r : Fin (v.header z d k D depth).ports) (parts : Fin attempts→Expr) :
    let head:=v.header z d k D depth
    (select head parts).eval m ((head.enum ⟨a,r⟩).val:Word w)=(parts a).eval m (r.val:Word w) := by
  let head:=v.header z d k D depth
  have row:=StripDirectory.header_pair head m load a r
  exact select_read head parts m _ _ a fit (by rw [row.1,Fin.val_cast_of_lt (a.isLt.trans_le fit)]) row.2

theorem Directory.archive_read (v : Directory attempts) (z d k D depth : ℕ) (m : Memory w)
    (load : (v.header z d k D depth).Loaded m) (fit : attempts≤2^w)
    (room : (v.header z d k D depth).ports≤2^w) (base : Fin attempts→ℕ)
    (a : Fin attempts) (r : Fin (v.header z d k D depth).ports) :
    let head:=v.header z d k D depth
    (v.archived z d k D depth base).eval m ((head.enum ⟨a,r⟩).val:Word w)=m (base a+r.val) := by
  let head:=v.header z d k D depth
  let terms : Fin attempts→Expr := fun t=>.lookup ⟨base t,ProtocolRAMPurchaseSampler.bits head.ports⟩ .row
  refine (v.dispatch z d k D depth m load fit a r terms).trans ?_
  change m (base a+(r.val:Word w).val%ProtocolRAMPurchaseSampler.span head.ports)=_
  rw [Fin.val_cast_of_lt (r.isLt.trans_le room),Nat.mod_eq_of_lt (r.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _))]

theorem Directory.fields_read (v : Directory attempts) (S : PurchaseSampler) (depth : ℕ) (m : Memory w)
    (groups : Fin K≃AllGroups z (2^W)) (a : Fin attempts) (r : Fin (count z (2^W) k*paths z S.degree depth))
    (side : Bool) (x : StageColumns z (2^W) × Role k attempts)
    (load : (v.header z (2^W) k S.degree depth).Loaded m) (fit : attempts≤2^w)
    (single : Reads (event v.remapBase v.keysBase (v.shelf a) S z (2^W) k depth a side) m (r.val:Word w) groups x) :
    let head:=v.header z (2^W) k S.degree depth
    Reads (v.fields S z W k depth side) m ((head.enum ⟨a,r⟩).val:Word w) groups x :=
  ⟨(v.dispatch z (2^W) k S.degree depth m load fit a r _).trans single.group,
    (v.dispatch z (2^W) k S.degree depth m load fit a r _).trans single.port,
    (v.dispatch z (2^W) k S.degree depth m load fit a r _).trans single.tag⟩

theorem Directory.reported (v : Directory attempts) (S : PurchaseSampler) (depth : ℕ)
    (groups : Fin K≃AllGroups z (2^W)) (packed : TaggedShorterSupergroups.Directory (reserved z W (ReportSockets.copies k attempts)) H)
    (π : Equiv.Perm (Fin (2^z))) (marks : Marks z W k attempts) (unique : Exclusive marks)
    (m : Memory w) (a : Fin attempts) (path : LiveChains S π depth (marks a))
    (r : Fin (count z (2^W) k*paths z S.degree depth))
    (load : (v.header z (2^W) k S.degree depth).Loaded m) (fit : attempts≤2^w)
    (sites : SiteROM.Resident packed v.sitesBase m)
    (tables : ∀g,let j:=((groups.symm g).val:Word w)
      (ProtocolRAMSupergroupDirectory.groupBank v.superBase K).read m j=((packed.group g).val:Word w) ∧
      (ProtocolRAMSupergroupDirectory.offsetBank v.superBase K).read m j=(packed.base g:Word w))
    (gFit : packed.groups≤2^w) (wordFit : packed.groups*H≤2^w)
    (ports : ∀side,Reads (event v.remapBase v.keysBase (v.shelf a) S z (2^W) k depth a side)
      m (r.val:Word w) groups (locate S π depth marks unique (.inr ⟨a,path⟩,side))) :
    let src := v.source S z W k depth K packed.groups H
    let head:=v.header z (2^W) k S.degree depth
    let ord:Word w:=(head.enum ⟨a,r⟩).val
    let chain : Row S π depth marks:=.inr ⟨a,path⟩
    src.group.eval m ord=((placed S π depth marks unique packed (chain,false)).1.val:Word w) ∧
      src.left.eval m ord=((siteNumber z (2^W) k (geometry S π depth marks chain false)).val:Word w) ∧
      src.right.eval m ord=((siteNumber z (2^W) k (geometry S π depth marks chain true)).val:Word w) := by
  intro src head ord chain
  let inputs:=v.fields S z W k depth
  have reads (s : Bool) := v.fields_read S depth m groups a r s _ load fit (ports s)
  have value (s : Bool) := SiteROM.catalogue_port packed v.sitesBase v.superBase groups m sites tables
    S π depth marks unique chain s (inputs s).group (inputs s).port (inputs s).tag ord gFit wordFit
    (reads s).group (reads s).port (reads s).tag
  refine ⟨?_,value false,value true⟩
  change (ProtocolRAMSupergroupDirectory.groupBank v.superBase K).read m ((inputs false).group.eval m ord)=_
  rw [(reads false).group]
  exact (tables (owner (locate S π depth marks unique (chain,false)).1)).1

end
end Hierarchy.ProtocolRAM.BoughtSockets

end OAI
