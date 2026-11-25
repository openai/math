import OAI.Hierarchy.DescentPrimaryTokenCoordinates
import OAI.Hierarchy.DescentRegisterArchiveValues
import OAI.Hierarchy.DescentResetRecordedPrimary
import OAI.Hierarchy.DescentPhysicalOperandMenu

namespace OAI
/-! Compact receiver, original root and node coordinates of a registered retained argument. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {a:PhysicalReset} {z:a.Atlas} {roots:a.RootInputs} (menu:OperandMenu z roots)
theorem target_book (j:Fin a.successor.setup.placement.shapes) :
    menu.target j=DescentResetActorClass.targetBook z.board a.successor.middle.rootDepth roots.Ht (j.cast menu.nodes):=by
  unfold target DescentResetActorClass.targetBook
  cases v:ActorSetup.shapeAt z.board a.successor.middle.rootDepth roots.Ht (j.cast menu.nodes) with
  | trunk b n=>cases b <;> cases n <;> rfl
  | good=>rfl
  | fall=>rfl

theorem keep_of_target (j:Fin a.successor.setup.placement.shapes) (n:ℕ) (found:menu.target j=some n) :
    menu.keep j=true:=by
  unfold target at found
  unfold keep
  split at found <;> simp_all
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty DescentSixParty.Chronology DescentKernelHistory DescentLocalArchiveOrder
open DescentCompiler DescentBundleHistory DescentCommonHost DescentDenseHostOrder DescentResetActorClass
open DescentSIMDLookup DescentRotor DescentDatedAddressBook DescentColonies
open DescentSixParty.ClosedReset.Window
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits}
  {G:PoweredGadget F} {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist p:ℕ}
  {input:Reached W G q ε S k i z D wire hist} {ctl:ResetRates G S k D n h C f g cut tail}
  (b:ClosedReset input ctl) (hp:0<p) (whole:p∣b.reset.unit) (a:Archive W) (old:Local a.bit)
local notation "Z" => b.reset
local notation "T" => b.terminals
local notation "next_" => (resetArchive b p hp whole a).bit
local notation "num" => DescentLocalArchiveOrder.reset b p hp whole a old
variable (ports:DatePorts) (room:DatePorts.RangeRoom ports b.next next_)
variable (x:Fin (2^ports.venue.k)) (slot:Fin ports.nodes) (h₁:Fin ports.operandHosts) (g₁:Fin ports.venue.groups)
  (now:NodeOrder.All next_) (prior:NodeOrder.All a.bit)
  (hit:DatePorts.slotAt ports b.next next_ num room x slot h₁ g₁=some now)
  (origin:resetOrigin b hp whole a now=Sum.inl prior)
local notation "t" => (T).home prior.1
local notation "actor" => (b.next.placement.pos now.1).2
local notation "hi" => (Z).rootBlock T (.inr t)
local notation:max "vertex" size:arg => b.frame.host.symm.toEmbedding.trans (input.vertex.trans (Fin.castLEEmb size))
local notation "nextGroup" => S.groupCount (i+1)
local notation "cc" => (T).commonDepth
local notation "res" => (Z).k-cc
local notation "height" => GroupStage.depthBound D n f g
variable {H:ℕ} (hosts:Fintype.card input.V≤H)
local notation "oldName" => input.vertex.trans (Fin.castLEEmb hosts)
local notation "primary" => (blocks b).src (trunkParent b t)
local notation "fd" => (Z).hostFields T (vertex hosts) actor

include hit origin in
theorem registered_primary_coordinates :
    ∃present:h₁.val<Fintype.card b.next.V,
      h₁.val=(b.next.vertex actor).val ∧
      (Z).rawAtIndex T (vertex hosts) ⟨h₁.val,present⟩=finProdFinEquiv fd ∧
      (fd).1=oldName (b.frame.host.symm ((T).code t).1) ∧
      DescentResetActorClass.targetBook ctl.board k height (((fd).2).cast b.public_hub_slots)=
        some (DescentFallbackShapeTable.cell res (DescentRelativeContacts.shortName cc ((T).code t)).2) ∧
      (g₁.val*2^k+x.val)=(hi).val ∧ slot.val=(num now.1 now.2).val ∧
      (g₁.cast room.groups.symm,x.cast (congrArg (2^·) room.radix.symm))=
        ((primary).1.1,(primary).2) ∧ actor=(primary).1.2:=by
  obtain ⟨atBlock,atNode,atHost,atGroup⟩:=DatePorts.slotAt_coordinates ports b.next next_ num room x slot h₁ g₁ now.1 now.2 hit
  have hostNum:h₁.val=(b.next.vertex actor).val:=congrArg Fin.val atHost
  let coarse:=(Z).orderedReentry T (DescentOrderedReset.grains W b.count b.order)
  have siteAt : coarse.graph.src (trunkParent b t)=((Z).resetNames T).symm (.inl (false,t)):=by
    apply ((Z).resetNames T).injective
    rw [Equiv.apply_symm_apply]
    exact (trunk_nodes b t).1
  have moved:=reached_node_site b hp whole a now
  rw [origin] at moved
  have here : primary=DescentSharedCableNames.Stage.home b.next.placement now.1:=by
    change DescentSharedCableNames.Stage.home b.next.placement (b.reblock.destination (coarse.graph.src (trunkParent b t)))=_
    rw [siteAt]
    exact congrArg (DescentSharedCableNames.Stage.home b.next.placement) moved
  refine ⟨by rw [hostNum];exact (b.next.vertex actor).isLt,hostNum,?_,?_,?_,?_,congrArg Fin.val atNode,?_,?_⟩
  · have ordered : (⟨h₁.val,by rw [hostNum];exact (b.next.vertex actor).isLt⟩:Fin (Fintype.card b.next.V))=
        (Z).denseHostRank T (vertex hosts) actor:=Fin.ext (hostNum.trans (dense_physical b hosts actor).symm)
    exact (congrArg ((Z).rawAtIndex T (vertex hosts)) ordered).trans ((Z).rawAtIndex_at T (vertex hosts) actor)
  · have published:=(physical_primary_fields b hp whole a hosts prior now origin).1
    have src:=b.frame.homeHost prior.1
    have dst: b.frame.host.symm ((T).code t).1=(input.placement.pos prior.1).2:=by rw [src,Equiv.symm_apply_apply]
    exact published.trans (congrArg (fun j : input.V => oldName j) dst.symm)
  · exact (physical_primary_fields b hp whole a hosts prior now origin).2
  · have place:=primary_raw_digits b hp whole a prior now origin
    let digits:=S.resetOutputDigits ctl.base ctl.radix b.age b.commonDepth
    have issued:=group_number b (finProdFinEquiv (digits hi))
    simp only [Equiv.symm_apply_apply] at issued
    simp only [atGroup,atBlock,Reached.NodeCells.coordinate,Fin.val_cast]
    rw [place] at issued
    have unpacked := (congrArg (fun z => (digits.symm z).val) place.symm).trans
      (congrArg Fin.val (digits.symm_apply_apply hi))
    simpa only [finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm] using issued.symm.trans unpacked
  · rw [here,atBlock,atGroup]
    simp only [Reached.NodeCells.coordinate,Fin.cast_cast,Fin.cast_refl,DescentSharedCableNames.Stage.home,id_eq]
  · exact congrArg (fun h=>h.1.2) here.symm


local notation "entry" => ((Z).denseHostRank T (vertex hosts)).trans (Fin.castLEEmb b.next.valid.host)
variable (pitch:ports.operandHosts=S.hostSize (i+1))
local notation "h₂" => h₁.cast pitch
local notation "x₂" => x.cast (congrArg (2^·) room.radix.symm)

include hit origin in
theorem registered_primary_cursors :
    h₂=entry (primary).1.2 ∧ g₁.cast room.groups.symm=(primary).1.1 ∧ x₂=(primary).2 ∧
    ((rackOf b entry h₂).map (fun v=>((g₁.cast room.groups.symm,v),x₂)))=some (DescentSharedCableNames.Stage.home b.next.placement now.1):=by
  obtain ⟨_,host,_,_,_,_,_,loc,same⟩:=
    registered_primary_coordinates b hp whole a old ports room x slot h₁ g₁ now prior hit origin hosts
  have selected:h₂=entry (primary).1.2:=by
    apply Fin.ext
    exact host.trans (by rw [same];exact (dense_physical b hosts (primary).1.2).symm)
  have gid:=congrArg Prod.fst loc
  have bid:=congrArg Prod.snd loc
  refine ⟨selected,gid,bid,?_⟩
  have paid := (congrArg (rackOf b entry) selected).trans (rack_present b entry (primary).1.2)
  refine (congrArg (Option.map (fun v => ((g₁.cast room.groups.symm,v),x₂))) paid).trans ?_
  change some ((g₁.cast room.groups.symm,(primary).1.2),x₂) = _
  obtain ⟨blockAt,_,_,groupAt⟩:=DatePorts.slotAt_coordinates ports b.next next_ num room x slot h₁ g₁ now.1 now.2 hit
  apply congrArg some
  rw [groupAt,blockAt,←same]
  simp only [Reached.NodeCells.coordinate,DescentSharedCableNames.Stage.home,Fin.cast_cast,Fin.cast_refl,id_eq]

end
end Hierarchy.DescentPrimitivePalette

end OAI
