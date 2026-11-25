import OAI.Hierarchy.TaggedWireOriginalRead

namespace OAI
/-! # The selected native core and acquired operands in the global role directory -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open AdaptiveProbe ReportSockets TaggedShorterSupergroups ProtocolRAM Calendar PurchaseCT
open ThreeFlat.RAM DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {w h W k attempts G K R H : ℕ} (S : PurchaseSampler) (L : Chart)

theorem paid_core (b : CatalogueRows.Board) (m : Memory w) (core bought : Bool→Socket)
    (i : Fin b.coreRows) (side : Bool) (p : PaidPorts S h W k attempts) (wide : b.rows<2^w)
    (loaded : Resolved S L (core side) m (i.val:Word w) (.inl p)) :
    Resolved S L (paidInputs b core bought side) m ((b.coreIndex i).val:Word w) (.inl p) := by
  apply resolved_congr S L m _ _ _ _ _ _ loaded
  funext j
  fin_cases j <;> exact b.select_core m _ _ i wide

theorem paid_bought (b : CatalogueRows.Board) (m : Memory w) (core bought : Bool→Socket)
    (i : Fin b.boughtRows) (side : Bool) (p : PaidPorts S h W k attempts) (wide : b.rows<2^w)
    (loaded : Resolved S L (bought side) m (i.val:Word w) (.inl p)) :
    Resolved S L (paidInputs b core bought side) m ((b.boughtIndex i).val:Word w) (.inl p) := by
  apply resolved_congr S L m _ _ _ _ _ _ loaded
  funext j
  fin_cases j <;> exact b.select_bought m _ _ i wide

/-- Resolve both the padded/private and CT-driven stage source from the same
ten header columns used by the core geometry reporter. -/
theorem core_read (order : Fin R≃Edges S h (2^W) k) (base freeBase bits superStart groupStart M : ℕ)
    (groups : Fin K≃AllGroups h (2^W)) (dir : Directory (reserved h W (copies k attempts)) H)
    (π : Equiv.Perm (Fin (2^h))) (depth : ℕ) (marks : Marks h W k attempts) (unique : Exclusive marks)
    (m : Memory w) (i : Fin R) (side : Bool)
    (header : CoreCatalogue.Header order base attempts groupStart M m) (geom : CoreCatalogue.Geometry π m (2^W))
    (directory : ReportGroupROM.Resident groupStart groups groupNumber m)
    (rowsFit : R≤2^w) (tileFit : 2^h≤2^w) (wide : 2^bits≤2^w) (one : (1:Word w)≠0)
    (ctEnd : Native.heapEnd h (2^W) Native.copies≤2^bits)
    (groupEnd : groupStart+ReportGroupROM.words h (2^W)≤2^bits)
    («public» : L.publicCount=Fintype.card (Public S h W k attempts)) (publicFit : L.publicCount≤2^w)
    (free : RoleROM.Mounted (freeBase+side.toNat*R) (freeTable S order attempts side) m)
    (sites : RoleROM.Mounted (L.publicBase+L.publicCount) (publicSites h W k attempts S) m)
    (codes : RoleROM.Mounted L.publicBase (RoleROM.publicTable S h W k attempts) m)
    (gs : L.groups=dir.groups) (ss : L.slots=H) (packedSites : SiteROM.Resident dir L.offBase m)
    (packedCodes : RoleROM.Mounted L.roleBase (RoleROM.positiveTable S dir) m)
    (super : ∀g,let j:=((groups.symm g).val:Word w)
      (ProtocolRAMSupergroupDirectory.groupBank superStart K).read m j=((dir.group g).val:Word w) ∧
      (ProtocolRAMSupergroupDirectory.offsetBank superStart K).read m j=(dir.base g:Word w))
    (gf : dir.groups≤2^w) (sf : dir.groups*H≤2^w) :
    Resolved S L (coreInputs base freeBase R bits superStart K k attempts side) m (i.val:Word w)
      (.inl (paid S π depth marks unique (.inl (order i),side))) := by
  cases hi : order i with
  | inl f=>
    have flag : (CoreCatalogue.field base R 0).eval m (i.val:Word w)=0 := by
      simpa [hi,CoreCatalogue.recordWord] using header.read rowsFit 0 i
    exact free_resolved S L order base freeBase bits superStart K m i f side hi flag «public» publicFit rowsFit free sites codes
  | inr r=>
    obtain ⟨⟨p,t⟩,l⟩:=r
    have flag : (CoreCatalogue.field base R 0).eval m (i.val:Word w)≠0 := by
      rw [(header.read rowsFit 0 i),hi]
      exact one
    obtain ⟨group,input,output,tagL,tagR⟩ := CoreCatalogue.operands order base bits attempts groupStart M groups π m
      header geom directory rowsFit tileFit wide ctEnd groupEnd i t p l hi
    cases side
    · apply packed_resolved S L dir superStart groups m _ _ _ _ _ _ _ flag gs ss packedSites packedCodes super gf sf
      · exact group
      · exact input
      · exact tagL
    · apply packed_resolved S L dir superStart groups m _ _ _ _ _ _ _ flag gs ss packedSites packedCodes super gf sf
      · exact group
      · exact output
      · exact tagR

open ProbeStage.Native PurchaseFrozen in
theorem bought_read (v : BoughtSockets.Directory attempts) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k attempts) (unique : Exclusive marks)
    (groups : Fin K≃AllGroups h (2^W)) (num : ReportGroupROM.Numbering h (2^W))
    (dir : Directory (reserved h W (ReportSockets.copies k attempts)) H)
    (m : Shelf.Mem h (2^W)) (e : Bought S π depth marks) (side : Bool)
    (data : (v.shelf e.1).PortData S π depth (BoughtLocation.keyOf e.2) m)
    (ct : BoughtSockets.numberLoaded num π m) (remap : ReportGroupROM.Resident v.remapBase groups num m)
    (header : (v.header h (2^W) k S.degree depth).Loaded m)
    (keys : (StripDirectory.stratumHeader h (2^W) k S.degree depth v.keysBase).Loaded m)
    (gs : L.groups=dir.groups) (ss : L.slots=H) (site : SiteROM.Resident dir L.offBase m)
    (code : RoleROM.Mounted L.roleBase (RoleROM.positiveTable S dir) m)
    (super : ∀g,let j:=((groups.symm g).val:Word (wordBits h (2^W) Native.copies))
      (ProtocolRAMSupergroupDirectory.groupBank v.superBase K).read m j=((dir.group g).val:Word _) ∧
      (ProtocolRAMSupergroupDirectory.offsetBank v.superBase K).read m j=(dir.base g:Word _))
    (attemptRoom : attempts≤2^wordBits h (2^W) Native.copies)
    (keyRoom : count h (2^W) k≤2^wordBits h (2^W) Native.copies)
    (tiles : (depth+1)*paths h S.degree depth≤2^wordBits h (2^W) Native.copies)
    (gf : dir.groups≤2^wordBits h (2^W) Native.copies) (sf : dir.groups*H≤2^wordBits h (2^W) Native.copies)
    (one : (1:Word (wordBits h (2^W) Native.copies))≠0) :
    let j := (v.header h (2^W) k S.degree depth).enum ⟨e.1,BoughtLocation.relative e.2⟩
    Resolved S L (boughtInputs v S h W k depth K side) m (j.val:Word _)
      (.inl (paid S π depth marks unique (.inr e,side))) := by
  have endpoint:=BoughtSockets.retained v.remapBase v.keysBase (v.shelf e.1) S π depth marks unique e.1 e.2
    groups num m ct remap data tiles keyRoom keys (BoughtLocation.localIndex e.2) (BoughtLocation.rows e.2) side
  have physical:=v.fields_read S depth m groups e.1 (BoughtLocation.relative e.2) side _ header attemptRoom endpoint
  exact bought_resolved S L v depth dir groups m _ _ side one gs ss site code super gf sf physical

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram

end
end OAI
