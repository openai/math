import OAI.Hierarchy.ProtocolRAMColumnSelectFits
import OAI.Hierarchy.ProtocolRAMRowChoiceFits
import OAI.Hierarchy.ProtocolRAMBoughtCatalogue
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! # Public read limits for native bought candidate and archival words -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage PurchaseFrozen PurchaseCT ReportSockets Calendar CatalogueRows
open scoped Classical Fin.CommRing
variable {z d k w attempts : ℕ}

private theorem bank_fits (b : Bank) {out : ℕ} (room : out<2^w) (endAt : b.base+b.size≤out) :
    b.Fits w out :=
  ⟨Nat.two_pow_pos _,by omega,endAt⟩

structure Directory.Cover (v : Directory attempts) (S : PurchaseSampler) (z W k depth K G H out : ℕ) : Prop where
  outer : (v.header z (2^W) k S.degree depth).stop≤ out
  keys : (StripDirectory.stratumHeader z (2^W) k S.degree depth v.keysBase).stop≤ out
  ct : Native.heapEnd z (2^W) Native.copies≤ out
  names : v.remapBase+ReportGroupROM.words z (2^W)≤ out
  source : ∀a (i : Key z (2^W) k),((v.shelf a).L S depth i).endAddress≤ out
  super : v.superBase+2*ProtocolRAMSupergroupDirectory.span K≤ out
  offsets : v.sitesBase+(SiteROM.offsets v.sitesBase G).size≤ out
  sites : v.sitesBase+G+(SiteROM.sites v.sitesBase G H).size≤ out
  flags : ∀ a,v.flagBase a+ProtocolRAMPurchaseSampler.span (v.header z (2^W) k S.degree depth).ports≤ out
  menus : ∀ a,v.menuBase a+ProtocolRAMPurchaseSampler.span (v.header z (2^W) k S.degree depth).ports≤ out

theorem Directory.source_fits (v : Directory attempts) (S : PurchaseSampler) (z W k depth K G H out : ℕ)
    (room : out<2^w) (C : v.Cover S z W k depth K G H out) :
    (v.source S z W k depth K G H).All (Expr.Fits w out) := by
  let head := v.header z (2^W) k S.degree depth
  have terms (a : Fin attempts) (i : Key z (2^W) k) (j : Fin (depth+1)) :
      (readTile (v.shelf a) S depth i j).Fits w out := by
    let L := (v.shelf a).L S depth i
    obtain ⟨_,_,_,_,_,so,ga,ta,en⟩ := L.regions
    have total : L.endAddress≤ out := C.source a i
    exact ⟨bank_fits L.source room (by omega),trivial,trivial⟩
  have ctb (i : Key z (2^W) k) (j : Fin 3) :
      (Native.stageBank z (2^W) (stageNumber (stage i)) j).Fits w out :=
    bank_fits _ room ((Native.stageBank_end z (2^W) (stageNumber (stage i)) j).trans C.ct)
  have one (a : Fin attempts) (i : Key z (2^W) k) (s : Bool) :
      let f := keyFields v.remapBase (v.shelf a) S depth i a s
      f.group.Fits w out ∧ f.port.Fits w out := by
    refine ⟨⟨bank_fits _ room ((remap_end v.remapBase (stage i)).trans C.names),ctb i 0,terms a i 0⟩,?_⟩
    cases s
    · exact ⟨ctb i 1,terms a i _⟩
    · exact ⟨ctb i 2,terms a i _⟩
  have stage (a : Fin attempts) (s : Bool) :
      let x := event v.remapBase v.keysBase (v.shelf a) S z (2^W) k depth a s
      x.group.Fits w out ∧ x.port.Fits w out ∧ x.tag.Fits w out :=
    ⟨select_fits _ _ room C.keys (fun i=>(one a i s).1),select_fits _ _ room C.keys (fun i=>(one a i s).2),trivial⟩
  let f := v.fields S z W k depth
  have two (s : Bool) : (f s).group.Fits w out ∧ (f s).port.Fits w out ∧ (f s).tag.Fits w out :=
    ⟨select_fits head _ room C.outer (fun a=>(stage a s).1),select_fits head _ room C.outer (fun a=>(stage a s).2.1),
      select_fits head _ room C.outer (fun a=>(stage a s).2.2)⟩
  have super := C.super
  have groups : (ProtocolRAMSupergroupDirectory.groupBank v.superBase K).Fits w out :=
    bank_fits _ room (by change v.superBase+ProtocolRAMSupergroupDirectory.span K≤ out;omega)
  have offsets : (ProtocolRAMSupergroupDirectory.offsetBank v.superBase K).Fits w out :=
    bank_fits _ room (by change v.superBase+ProtocolRAMSupergroupDirectory.span K+ProtocolRAMSupergroupDirectory.span K≤ out;omega)
  have mult (n : ℕ) (e : Expr) (fit : e.Fits w out) : (scale n e).Fits w out := by
    induction n with
    | zero => trivial
    | succ n ih => exact ⟨fit,ih⟩
  have side (s : Bool) : (SiteROM.atPort v.sitesBase G H v.superBase K (ReportSockets.copies k attempts)
      (f s).group (f s).port (f s).tag).Fits w out := by
    obtain ⟨g,p,t⟩ := two s
    exact ⟨bank_fits _ room C.sites,⟨bank_fits _ room C.offsets,groups,g⟩,⟨offsets,g⟩,mult 1 _ ⟨t,mult _ _ p⟩⟩
  have archive (localBase : Fin attempts→ℕ) (ends : ∀a,localBase a+ProtocolRAMPurchaseSampler.span head.ports≤ out) :
      (v.archived z (2^W) k S.degree depth localBase).Fits w out :=
    select_fits _ _ room C.outer (fun a=>⟨bank_fits _ room (ends a),trivial⟩)
  exact ⟨⟨groups,(two false).1⟩,side false,side true,archive _ C.flags,archive _ C.menus⟩

end Hierarchy.ProtocolRAM.BoughtSockets
end

end OAI
