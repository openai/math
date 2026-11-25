import OAI.Hierarchy.DescentNamedResetDateInputs
import OAI.Hierarchy.DescentPriorResetArchive
import OAI.Hierarchy.DescentPhysicalResetDate

namespace OAI
/-! A numerical final emitter using the actually published primitive and stage-venue banks. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentCompiler DescentSixParty DescentPackedWalsh DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Stage DescentResetGates ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "cc" => S.groupWidth k tail age
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "start" => (a).stageStart floor
local notation "b" => (a).rebased start
local notation "v" => (a).successor
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (prevMeta prevArgs : ℕ) (seed : Bool)
local notation "inputs" pr:arg sc:arg => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prevMeta prevArgs seed pr sc

/-- The seed width, grain bound, and rotor are the global tag alphabet used by the seed,
ordinary dates, and the same date's final primitive lookup. -/
def FinalInputs.fromNamed (prepared : (rc).PreparedFits book)
    (scene : (v).front.SceneRoom ((v).actorEnd b) ((v).issuedScene b older) w)
    (archive : PriorRolePages) (seedWidth grain : ℕ) (op : RotorSpec)
    (capacity : venue.cap=cap) : (inputs prepared scene).FinalInputs where
  menu:={ F := F, gadget := G, stageBits := seedWidth, grain := grain, op := op }
  previousRoleBase:=archive.first
  previousRoleStride:=archive.stride
  previousRoleBits:=archive.bits
  roleNodes:=rfl
  roleBlocks:=rfl
  classShape:=rfl
  primaryRanks:=rfl
  guardRoots:=rfl
  guardDepth:=rfl
  birthNodes:=rfl
  birthBlocks:=rfl
  birthArgs:=rfl
  censusBlocks:=rfl
  censusNodes:=rfl
  io:=io
  signedCount:=by change venue.cap=(2*cap)/2;rw [capacity];omega
  roleCount:=rfl
  metaBlocks:=rfl
  metaNodes:=rfl

local notation "emit" pr:arg sc:arg => FinalInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prevMeta prevArgs seed pr sc

set_option maxRecDepth 4096 in
theorem FinalInputs.fromNamed_pages (prepared : (rc).PreparedFits book)
    (scene : (v).front.SceneRoom ((v).actorEnd b) ((v).issuedScene b older) w)
    (archive : PriorRolePages) (seedWidth grain : ℕ) (op : RotorSpec)
    (capacity : venue.cap=cap) :
    let z:=(emit prepared scene) archive seedWidth grain op capacity
    z.io=io ∧ (∀j,z.earlier j=DescentFundedCensus.priorBank io j.val) ∧
      (∀j,z.previousRoles j=archive.bank j.val) :=⟨rfl,fun _=>rfl,fun _=>rfl⟩

theorem FinalInputs.fromNamed_role_room (prepared : (rc).PreparedFits book)
    (scene : (v).front.SceneRoom ((v).actorEnd b) ((v).issuedScene b older) w)
    (archive : PriorRolePages) (seedWidth grain : ℕ) (op : RotorSpec)
    (capacity : venue.cap=cap) (blocks : (v).roleTransfer.transfer.blocks≤archive.blocks)
    (earlier : archive.endAddress≤ start) (space : start<2^w) :
    let z:=(emit prepared scene) archive seedWidth grain op capacity
    ∀j,(z.previousRoles j).Fits w start:=
  fun j=>archive.fits w start j.val (j.isLt.trans_le blocks) earlier space

/-- Opening the three physical output pages of a preceding seed, ordinary, or
reset date supplies all four earlier registers of the full date. -/
def FinalInputs.fromArchive (prepared : (rc).PreparedFits book)
    (scene : (v).front.SceneRoom ((v).actorEnd b) ((v).issuedScene b older) w)
    (history : PriorResetArchive) (seedWidth grain : ℕ) (op : RotorSpec)
    (capacity : venue.cap=cap) :=
  FinalInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    history.nodeBase history.arguments history.seed prepared scene history.roles seedWidth grain op capacity

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
