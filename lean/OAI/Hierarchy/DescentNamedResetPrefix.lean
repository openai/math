import OAI.Hierarchy.DescentResetVenueEnd
import OAI.Hierarchy.DescentNamedResetAtlas
import OAI.Hierarchy.DescentResetRootsFromVenue
import OAI.Hierarchy.DescentResetReceiverPitch
import OAI.Hierarchy.DescentResetCanvasIngress
import OAI.Hierarchy.DescentStageVenueWireRoom

namespace OAI
/-! # Prefix of the original private-root scan at a selected reset -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentPackedWalsh
open DescentColonies DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false

/-- All the stages after the root scan are appended to the same date. -/
theorem ResetOutput.projection_before_metadata (v : ResetOutput) (b : ℕ) :
    v.middle.afterProjection b≤v.metadataEnd b:=by
  let md:=v.middle
  have hdr : md.afterProjection b≤ md.rootHeader (md.afterProjection b):=by
    change _≤rootHeaderEnd _ _ _ _ _ _ _ _ _ _
    rw [root_header_affine]
    exact Nat.le_add_right ..
  have finish:md.rootHeader (md.afterProjection b)≤ md.stop b:=by
    change _≤RootTemplates.privateEnd _ _ _ _ _ _ _
    unfold RootTemplates.privateEnd RootArena.first RootTemplates.arena
    exact Nat.le_add_right ..
  obtain ⟨t,r,end_⟩:=v.earlier b
  have us:=v.final_ge b
  obtain ⟨fund,ven⟩:=v.complete_after b
  exact (hdr.trans finish).trans (t.trans (r.trans (end_.trans (us.trans (fund.trans (ven.trans (v.venue_before_metadata b)))))))

namespace PhysicalReset
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
    (io : Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "o" => (a).successor
local notation "md" => (o).middle
local notation "oldCap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "cc" => S.groupWidth k tail age
local notation "dep" => GroupStage.depthBound venue.degree n f g
local notation "root_" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor
local notation "at_" => (a).stageStart floor

/-- The checkpoint uses the one-based tokens produced by the ingress. The private
root scan uses the original signed banks, in their original packing. -/
theorem named_prefix (sh : (a).StencilShape) (count : Bank) (batch : e≤previous) (oldCut : previous≤cc)
    (groups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (priorWire : ∀(x : Block k) (j : Fin (2*oldCap)),
      (io.wire x.val j.val).Fits w floor ∧ S.hostSize age*chunks (S.groupCount age) (2^previous)≤(io.wire x.val j.val).size)
    (selected : ∀t∈(o).rootUnits,t*2^e≤w/2) (space : (a).fullEnd floor<2^w) :
    ((a).rootPhase sh at_ count io.hubs g (2^n) (root_ batch oldCut) w).PrefixFits:=by
  have cap : (a).c/2=oldCap:=by change (2*oldCap)/2=oldCap;omega
  have shape : (a).RootShape:=by
    refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩ <;> rw [cap] <;> rfl
  have entry : floor≤at_ := by
    obtain ⟨h₁,h₂,h₃⟩:=(a).ingress.order floor
    exact (h₁.trans h₂).trans h₃
  have toRebase : at_≤(a).rebased at_:=((a).occupied at_).1.trans ((a).occupied at_).2.1
  have startBound : floor≤((a).stencilPhase sh at_ count io.hubs g (2^n)).endAddress:=by
    rw [(a).stencil_end]
    change floor≤(md).stencil.endAddress ((a).rebased at_)
    have aug:=(md).stencil.translated 0 ((a).rebased at_)
    rw [Nat.zero_add] at aug
    rw [aug]
    omega
  have price₁: (md).projectBits*2^e≤w/2:=selected _ (by simp [ResetOutput.rootUnits])
  let ar:=DescentFallbackPeriod.Projected.Receiver.arityLimit (md).rootDegree (2^(md).rootDepth) (o).front.donor.cap (md).rotorBits (md).rootDepth
  have receipt:(md).rootField*(ar+1)*2^e≤w/2:=selected _ (by simp [ResetOutput.rootUnits,ar])
  have price₂:(md).rootField*2^e≤w/2:= (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos ar))).trans receipt
  have dims : DescentFallbackPeriod.Projected.maxBits (md).stencil.t (a).ports ((a).c/2) (2^(md).rootDepth)=(md).projectBits:=by
    unfold DescentFallbackPeriod.Projected.maxBits ResetMiddle.projectBits
    rw [shape.bits]
  have word : ((a).rootPhase sh at_ count io.hubs g (2^n) (root_ batch oldCut) w).projectionEnd<2^w:=by
    rw [(a).projection_end sh at_ count io.hubs g (2^n) (root_ batch oldCut) shape w]
    exact ((o).projection_before_metadata ((a).rebased at_)).trans_lt space
  apply RootInputs.prefix_from_venue («a»:=a) sh at_ count io.hubs g (2^n) io dep _ _ _ w shape floor startBound
  · intro x j
    let slot : Fin (2*oldCap):=j.cast (congrArg (2*·) cap)
    have banks:=priorWire x slot
    refine ⟨banks.1,?_⟩
    change S.hostSize age*chunks (2^cc) (2^(previous-e)*2^e)≤_
    rw [S.group_power groups radix,←pow_add,Nat.sub_add_cancel batch]
    exact banks.2
  · change cc=cc-e+e
    omega
  · rfl
  · rw [dims]
    change 2^e*max (md).projectBits (md).rootField≤w/2
    rcases le_total (md).projectBits (md).rootField with le | le
    · rwa [max_eq_right le,Nat.mul_comm]
    · rwa [max_eq_left le,Nat.mul_comm]
  · exact word

end PhysicalReset
end
end Hierarchy.DescentDatedAddressBook

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh
open DescentColonies DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h : ℕ)
    (previous nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
    (io : Dated.Operands) (floor w : ℕ)
local notation "cut_" => receiverCut G S board k tail age p f g drift degree h previous nextM C packet
  oldLanes primitiveLanes printedBits venue
local notation "issued_" => selected G S board k tail age p f g drift degree h previous nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "cc" => S.groupWidth k tail age
local notation "oldCap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "params_" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "fields_" => ResetOutput.fromBoard G S board k tail age p f g drift degree h
  0 previous 1 nextM C packet params_ 0
local notation "picked_" => selected_cut G S board k tail age p f g drift degree h previous nextM C packet
  oldLanes primitiveLanes printedBits venue
local notation "head_" => namedRoots G S board k tail age p f g drift degree h cut_ previous (2^cut_) nextM C packet
  oldLanes primitiveLanes printedBits venue io floor
local notation "shape_" => namedStencil G S board k tail age p f g drift degree h cut_ previous (2^cut_) nextM C packet
  oldLanes primitiveLanes printedBits venue io floor (picked_).2.1

/-- The executable cut computes both the current pitch and all the dictionary
word bounds from the original input size. -/
theorem selected_prefix (count : Bank) (prev : previous≤cc) (groups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (priorWire : ∀(x : Block k) (j : Fin (2*oldCap)),
      (io.wire x.val j.val).Fits w floor ∧ S.hostSize age*chunks (S.groupCount age) (2^previous)≤(io.wire x.val j.val).size)
    (small : 8*(fields_).groupWidth≤h) (word : h≤w) (space : (issued_).fullEnd floor<2^w) :
    ((issued_).rootPhase shape_ ((issued_).stageStart floor) count io.hubs g (2^n) (head_ (picked_).1 prev) w).PrefixFits:=by
  apply named_prefix G S board k tail age p f g drift degree h cut_ previous (2^cut_) nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w shape_ count (picked_).1 prev groups radix priorWire _ space
  intro t live
  have charged:=selected_room G S board k tail age p f g drift degree h previous nextM C packet
    oldLanes primitiveLanes printedBits venue io.wire io.roster floor t small (Or.inl live)
  exact charged.trans (Nat.div_le_div_right word)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
