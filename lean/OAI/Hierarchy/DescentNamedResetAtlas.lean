import OAI.Hierarchy.DescentNamedResetOutput
import OAI.Hierarchy.DescentResetAtlasMenu
import OAI.Hierarchy.DescentResetRootsFromVenue

namespace OAI
/-! # Publicly indexed reset root tables on the native precursor -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentWalshPrecision DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Stage DescentResetGates ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
    (io : Dated.Operands) (floor : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "mid" => (a).successor.middle
local notation "cc" => S.groupWidth k tail age
local notation "oldCap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "dep" => GroupStage.depthBound venue.degree n f g
local notation "lane" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
local notation "chunk" => ResetInput.calendarLanes S G.b (age+1)

/-- The public stencil geometry follows from the chosen dyadic payload exponent. -/
theorem namedStencil (batch : e≤lane-k) : (a).StencilShape :=by
  have dim : lane≤cc+k:=Nat.min_le_left _ _
  refine StencilShape.of_dyadic a rfl rfl (Nat.sub_add_cancel dim).symm rfl ?_ rfl rfl ?_
  · change _*2^(cc+k-cc)=_*2^k
    rw [Nat.add_sub_cancel_left]
    rfl
  · change lane-k-e+e≤cc
    omega

/-- The signed root lookup reads the previous native stage's standard wire
bank in its original packing. Its original packing is exactly (2^{previous}). -/
def namedRoots (batch : e≤previous) (width : previous≤cc) : (a).RootInputs :=
  RootInputs.fromVenue a io dep (Nat.two_pow_pos _) (Nat.two_pow_pos _) (by
    change 2^cc=(2^cc/(2^(previous-e)*2^e))*(2^(previous-e)*2^e)
    rw [←pow_add,Nat.sub_add_cancel batch]
    exact (Nat.div_mul_cancel (pow_dvd_pow 2 width)).symm)

local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor

/-- The selected post-remix chart, both rotor op families and the count of
packets are read by the official atlas constructor on this stage. -/
def namedAtlas (sh : (a).StencilShape) (count : Bank) : (a).Atlas :=
  Atlas.menu a sh ((a).stageStart floor) count io.hubs g (2^n) board rfl packet C chunk
    (32*Nat.clog 2 (2*venue.degree))

local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor

/-- These equalities expose the numeric menu, root rows, and both native
packing cardinalities without access to a hidden branch or to RAM contents. -/
theorem named_root_facts (batch : e≤previous) (width : previous≤cc) (sh : (a).StencilShape) (count : Bank) :
    let root:=roots batch width
    let menu:=atlas sh count
    let _phase:=(a).stencilPhase sh ((a).stageStart floor) count io.hubs g (2^n)
    root.Ht=dep ∧ root.field=ResetMiddle.fieldWidth venue.degree oldCap n k dep ∧
    (∀s x,root.old s x=io.wire x.val s.val) ∧
    menu.boardDegree=d ∧ HEq menu.board board ∧ menu.packet=packet ∧ menu.C=C ∧ menu.groupDigits=chunk ∧
    menu.batches=DescentRecordedRotorLayers.layers n packet f oldCap*chunk ∧
    menu.layerBits=DescentRecordedRotorLayers.width f oldCap ∧ menu.factor=32*Nat.clog 2 (2*venue.degree) ∧
    (∀t,HEq (menu.primitive t) (Atlas.roleCode n t)) ∧
    (∀ w,
      let book := atlasBook menu sh ((a).stageStart floor) count io.hubs g (2^n) root w
      book.fallbackDegree=32*Nat.clog 2 (2*venue.degree) ∧ book.hubBits=g ∧
        book.loadBits=f ∧ book.shapes=2^dep) :=by
  intro root menu _phase
  have logical:(a).c/2=oldCap:=by change (2*oldCap)/2=oldCap;omega
  refine ⟨rfl,rfl,fun _ _=>rfl,rfl,HEq.rfl,rfl,rfl,rfl,?_,?_,rfl,fun _=>HEq.rfl,fun _=>?_⟩
  · change DescentRecordedRotorLayers.layers n packet f ((a).c/2)*chunk=_
    rw [logical]
  · change DescentRecordedRotorLayers.width f ((a).c/2)=_
    rw [logical]
  · exact ⟨rfl,rfl,rfl,rfl⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
