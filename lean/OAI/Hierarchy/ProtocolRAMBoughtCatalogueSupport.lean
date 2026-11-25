import OAI.Hierarchy.ProtocolRAMBoughtCatalogue
import OAI.Hierarchy.ProtocolRAMBoughtLocations
import OAI.Hierarchy.ProtocolRAMCataloguePruning

namespace OAI
/-! # Each paid chronological catalogue row names its unique acquired chain -/

namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen ReportSockets ProbeStage.CoreBoard
open TaggedShorterSupergroups Calendar Calendar.CatalogueRows
open scoped Fin.CommRing Classical
noncomputable section
variable {z W k attempts K H : ℕ}

private theorem located_words (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth M : ℕ)
    (marks : Marks z W k attempts) (e : Bought S π depth marks) {w : ℕ} (src : BoughtSource) (m : Memory w) (r : Word w)
    (room : siteLast z (2^W) k+1≤2^w)
    (left : src.left.eval m r=((siteNumber z (2^W) k (geometry S π depth marks (.inr e) false)).val:Word w))
    (right : src.right.eval m r=((siteNumber z (2^W) k (geometry S π depth marks (.inr e) true)).val:Word w)) :
    Located S π depth marks M (src.view m r) (.inr e) := by
  refine ⟨?_,?_,rfl⟩
  · change (src.left.eval m r).val=_
    rw [left,Fin.val_cast_of_lt ((siteNumber z (2^W) k _).isLt.trans_le room)]
    rfl
  · change (src.right.eval m r).val=_
    rw [right,Fin.val_cast_of_lt ((siteNumber z (2^W) k _).isLt.trans_le room)]
    rfl

/-- The conjunction directly identifies the corresponding row of the endpoint
serializer. Its chronological address is the same fixed original ordinal
used by the paid terminal catalogue, on both sides of the edge. -/
theorem Directory.located_original (v : Directory attempts) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth M : ℕ) (marks : Marks z W k attempts) (unique : Exclusive marks)
    (groups : Fin K≃AllGroups z (2^W)) (num : ReportGroupROM.Numbering z (2^W))
    (packed : TaggedShorterSupergroups.Directory (reserved z W (ReportSockets.copies k attempts)) H)
    (terminal : Shelf.Mem z (2^W)) (e : Bought S π depth marks)
    (data : (v.shelf e.1).PortData S π depth (BoughtLocation.keyOf e.2) terminal)
    (ct : numberLoaded num π terminal) (remap : ReportGroupROM.Resident v.remapBase groups num terminal)
    (outer : (v.header z (2^W) k S.degree depth).Loaded terminal)
    (keys : (StripDirectory.stratumHeader z (2^W) k S.degree depth v.keysBase).Loaded terminal)
    (sites : SiteROM.Resident packed v.sitesBase terminal)
    (tables : ∀g,let j:=((groups.symm g).val:Word (wordBits z (2^W) Native.copies))
      (ProtocolRAMSupergroupDirectory.groupBank v.superBase K).read terminal j=((packed.group g).val:Word _) ∧
      (ProtocolRAMSupergroupDirectory.offsetBank v.superBase K).read terminal j=(packed.base g:Word _))
    (events : attempts≤2^wordBits z (2^W) Native.copies)
    (keySize : count z (2^W) k≤2^wordBits z (2^W) Native.copies)
    (tileSize : (depth+1)*paths z S.degree depth≤2^wordBits z (2^W) Native.copies)
    (gFit : packed.groups≤2^wordBits z (2^W) Native.copies) (sFit : packed.groups*H≤2^wordBits z (2^W) Native.copies)
    (siteFit : siteLast z (2^W) k+1≤2^wordBits z (2^W) Native.copies) :
    let src:=v.source S z W k depth K packed.groups H
    let r:=(v.header z (2^W) k S.degree depth).enum ⟨e.1,BoughtLocation.relative e.2⟩
    Located S π depth marks M (src.view terminal (r.val:Word _)) (.inr e) := by
  have sides (s : Bool) := retained v.remapBase v.keysBase (v.shelf e.1) S π depth marks unique e.1 e.2 groups num terminal
    ct remap data tileSize keySize keys (BoughtLocation.localIndex e.2) (BoughtLocation.rows e.2) s
  have ends:=v.reported S depth groups packed π marks unique terminal e.1 e.2 (BoughtLocation.relative e.2)
    outer events sites tables gFit sFit sides
  exact located_words S π depth M marks e _ terminal _ siteFit ends.2.1 ends.2.2

/-- Inverse of the chronological source-row injection, at the exact ordinal
required for charging a visible fee only once. -/
theorem Directory.active_original (v : Directory attempts) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (marks : Marks z W k attempts) (terminal : Shelf.Mem z (2^W))
    (phase : Fin attempts→PhasePrice) (T : Fin attempts→ℝ) (kind mode : Fin attempts→ℕ)
    (frozen fixture : Fin attempts→Shelf.Mem z (2^W))
    (meaning : ∀a,mode a=3 → marks a=StripDirectory.actualMarks (v.shelf a) (phase a) (T a) (kind a) (frozen a))
    (incoming : ∀a,(v.shelf a).Incoming (k:=k) S π depth (phase a) (T a) (kind a) (frozen a))
    (prepare : ∀a (i : Key z (2^W) k),(v.shelf a).Prepared S depth (fixture a) i (frozen a))
    (room : ∀a,(v.shelf a).flagsBase S z (2^W) k depth+count z (2^W) k*paths z S.degree depth<2^wordBits z (2^W) Native.copies)
    (archive : ∀a (r : Fin (count z (2^W) k*paths z S.degree depth)),terminal (v.flagBase a+r.val)=
      if mode a=3 then (v.shelf a).result S k depth (frozen a) ((v.shelf a).flagsBase S z (2^W) k depth+r.val) else 0)
    (outer : (v.header z (2^W) k S.degree depth).Loaded terminal) (events : attempts≤2^wordBits z (2^W) Native.copies)
    (j : Fin (v.header z (2^W) k S.degree depth).count)
    (live : (v.archived z (2^W) k S.degree depth v.flagBase).eval terminal (j.val:Word _)≠0) :
    ∃e : Bought S π depth marks,(v.header z (2^W) k S.degree depth).enum ⟨e.1,BoughtLocation.relative e.2⟩=j := by
  let head:=v.header z (2^W) k S.degree depth
  obtain ⟨⟨a,r⟩,rfl⟩ := head.enum.surjective j
  have bound : head.ports≤2^wordBits z (2^W) Native.copies := by have := room a;change _+head.ports<_ at this;omega
  have same:=v.archive_read z (2^W) k S.degree depth terminal outer events bound v.flagBase a r
  change (v.archived z (2^W) k S.degree depth v.flagBase).eval terminal _≠0 at live
  rw [same,archive a r] at live
  have selected : mode a=3 := by by_contra no;exact live (ite_eq_right no)
  rw [ite_eq_left selected] at live
  have represented : ∃p : LiveChains S π depth (marks a), BoughtLocation.relative p=r := by
    rw [meaning a selected]
    let E := BoughtLocation.resultEquiv (v.shelf a) S π depth (Nat.two_pow_pos _)
      (phase a) (T a) (kind a) (frozen a) (fixture a) (incoming a) (prepare a) (room a)
    let p:=E.symm ⟨r,live⟩
    exact ⟨p,congrArg Subtype.val (E.apply_symm_apply ⟨r,live⟩)⟩
  obtain ⟨p,row⟩ := represented
  exact ⟨⟨a,p⟩,congrArg (fun u=>head.enum ⟨a,u⟩) row⟩

private theorem relative_cast {d : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    {m m' : StageAt z d→Fin k×Bool→Finset (Fin (2^z))} (same : m=m') (p : LiveChains S π depth m) :
    BoughtLocation.relative (Equiv.cast (congrArg (LiveChains S π depth) same) p)=BoughtLocation.relative p := by
  cases same
  rfl

theorem mode_of_chain {d : ℕ} (mode : ℕ) (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen : Shelf.Mem z d)
    (p : LiveChains S π depth (Shelf.catalogueMarks (k:=k) mode sh phase T kind frozen)) : mode=3 := by
  by_contra no
  exact (Fintype.card_eq_zero_iff.mp (Shelf.card_liveChains_idle mode sh S π depth phase T kind frozen no)).false p

theorem catalogueEquiv_val {d : ℕ} (mode : ℕ) (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (hd : 1≤d) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (frozen fixture archive : Shelf.Mem z d) (base : ℕ) (input prepared room flags)
    (p : LiveChains S π depth (Shelf.catalogueMarks (k:=k) mode sh phase T kind frozen)) :
    ((BoughtLocation.catalogueEquiv mode sh S π depth hd phase T kind frozen fixture archive base input prepared room flags) p).val=
      BoughtLocation.relative p := by
  have buy := mode_of_chain mode sh S π depth phase T kind frozen p
  rw [BoughtLocation.catalogueEquiv_val_of_buy mode sh S π depth hd phase T kind frozen fixture archive base input prepared room flags p buy]
  exact relative_cast S π depth (Shelf.catalogueMarks_buy mode sh phase T kind frozen buy) p

/-- A live chain at the observed mode necessarily comes from a buy event.
The native flag at the chain's own original chronological ordinal is nonzero. -/
theorem Directory.original_active (v : Directory attempts) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth K₀ G width : ℕ) (terminal : Shelf.Mem z (2^W))
    (phase : Fin attempts→PhasePrice) (T : Fin attempts→ℝ) (kind mode : Fin attempts→ℕ)
    (frozen fixture : Fin attempts→Shelf.Mem z (2^W))
    (incoming : ∀a,(v.shelf a).Incoming (k:=k) S π depth (phase a) (T a) (kind a) (frozen a))
    (prepare : ∀a (i : Key z (2^W) k),(v.shelf a).Prepared S depth (fixture a) i (frozen a))
    (room : ∀a,(v.shelf a).flagsBase S z (2^W) k depth+count z (2^W) k*paths z S.degree depth<2^wordBits z (2^W) Native.copies)
    (archive : ∀a (r : Fin (count z (2^W) k*paths z S.degree depth)),terminal (v.flagBase a+r.val)=
      if mode a=3 then (v.shelf a).result S k depth (frozen a) ((v.shelf a).flagsBase S z (2^W) k depth+r.val) else 0)
    (outer : (v.header z (2^W) k S.degree depth).Loaded terminal) (events : attempts≤2^wordBits z (2^W) Native.copies)
    (e : Bought S π depth (fun a↦Shelf.catalogueMarks (k:=k) (mode a) (v.shelf a) (phase a) (T a) (kind a) (frozen a))) :
    let h:=v.header z (2^W) k S.degree depth
    let src:=v.source S z W k depth K₀ G width
    mode e.1=3 ∧ src.flag.eval terminal ((h.enum ⟨e.1,BoughtLocation.relative e.2⟩).val:Word _)≠0 := by
  intro h src
  let a:=e.1
  have buy:=mode_of_chain (mode a) (v.shelf a) S π depth (phase a) (T a) (kind a) (frozen a) e.2
  refine ⟨buy,?_⟩
  have capacity : h.ports≤2^wordBits z (2^W) Native.copies := by have := room a;change _+h.ports<_ at this;omega
  have read:=v.archive_read z (2^W) k S.degree depth terminal outer events capacity v.flagBase a (BoughtLocation.relative e.2)
  change (v.archived z (2^W) k S.degree depth v.flagBase).eval terminal _≠0
  rw [read]
  let E:=BoughtLocation.catalogueEquiv (mode a) (v.shelf a) S π depth (Nat.two_pow_pos _) (phase a) (T a) (kind a)
    (frozen a) (fixture a) terminal (v.flagBase a) (incoming a) (prepare a) (room a) (archive a)
  have original : (E e.2).val=BoughtLocation.relative e.2:=catalogueEquiv_val (mode a) (v.shelf a) S π depth (Nat.two_pow_pos _) (phase a) (T a) (kind a)
    (frozen a) (fixture a) terminal (v.flagBase a) (incoming a) (prepare a) (room a) (archive a) e.2
  exact original ▸ (E e.2).property

/-- These equalities concern permanent calendar outputs. The calendar proves
the first equality by its own mode-gated flag write and subsequent frame. -/
theorem Directory.active_located (v : Directory attempts) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth M : ℕ) (marks : Marks z W k attempts) (unique : Exclusive marks)
    (groups : Fin K≃AllGroups z (2^W)) (num : ReportGroupROM.Numbering z (2^W))
    (packed : TaggedShorterSupergroups.Directory (reserved z W (ReportSockets.copies k attempts)) H)
    (terminal : Shelf.Mem z (2^W)) (phase : Fin attempts→PhasePrice) (T : Fin attempts→ℝ) (kind mode : Fin attempts→ℕ)
    (frozen fixture : Fin attempts→Shelf.Mem z (2^W))
    (meaning : ∀ a,mode a=3 → marks a=StripDirectory.actualMarks (v.shelf a) (phase a) (T a) (kind a) (frozen a))
    (incoming : ∀a,(v.shelf a).Incoming (k:=k) S π depth (phase a) (T a) (kind a) (frozen a))
    (prepare : ∀a (i : Key z (2^W) k),(v.shelf a).Prepared S depth (fixture a) i (frozen a))
    (room : ∀a,(v.shelf a).flagsBase S z (2^W) k depth+count z (2^W) k*paths z S.degree depth<2^wordBits z (2^W) Native.copies)
    (archive : ∀a (r : Fin (count z (2^W) k*paths z S.degree depth)),terminal (v.flagBase a+r.val)=
      if mode a=3 then (v.shelf a).result S k depth (frozen a) ((v.shelf a).flagsBase S z (2^W) k depth+r.val) else 0)
    (data : ∀a (i : Key z (2^W) k),(v.shelf a).PortData S π depth i terminal) (ct : numberLoaded num π terminal)
    (remap : ReportGroupROM.Resident v.remapBase groups num terminal)
    (outer : (v.header z (2^W) k S.degree depth).Loaded terminal)
    (keys : (StripDirectory.stratumHeader z (2^W) k S.degree depth v.keysBase).Loaded terminal)
    (sites : SiteROM.Resident packed v.sitesBase terminal)
    (tables : ∀g,let j:=((groups.symm g).val:Word (wordBits z (2^W) Native.copies))
      (ProtocolRAMSupergroupDirectory.groupBank v.superBase K).read terminal j=((packed.group g).val:Word _) ∧
      (ProtocolRAMSupergroupDirectory.offsetBank v.superBase K).read terminal j=(packed.base g:Word _))
    (events : attempts≤2^wordBits z (2^W) Native.copies)
    (keySize : count z (2^W) k≤2^wordBits z (2^W) Native.copies)
    (tileSize : (depth+1)*paths z S.degree depth≤2^wordBits z (2^W) Native.copies)
    (gFit : packed.groups≤2^wordBits z (2^W) Native.copies) (sFit : packed.groups*H≤2^wordBits z (2^W) Native.copies)
    (siteFit : siteLast z (2^W) k+1≤2^wordBits z (2^W) Native.copies)
    (j : Fin (v.header z (2^W) k S.degree depth).count) :
    let src:=v.source S z W k depth K packed.groups H
    src.flag.eval terminal (j.val:Word _)≠0 →
      ∃ chain : Bought S π depth marks, Located S π depth marks M (src.view terminal (j.val:Word _)) (.inr chain) := by
  intro src live
  obtain ⟨e,rfl⟩ := v.active_original S π depth marks terminal phase T kind mode frozen fixture
    meaning incoming prepare room archive outer events j live
  exact ⟨e,v.located_original S π depth M marks unique groups num packed terminal e (data e.1 _)
    ct remap outer keys sites tables events keySize tileSize gFit sFit siteFit⟩

end
end Hierarchy.ProtocolRAM.BoughtSockets

end OAI
