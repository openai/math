import OAI.Hierarchy.DescentNamedIngressCode
import OAI.Hierarchy.DescentNamedFinalInputs

namespace OAI
/-! # One issued reset, including the retiled ports and the restored primitive and argument pages -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentCompiler DescentSixParty DescentPackedWalsh DescentSIMDLookup
open DescentSixParty.Chronology DescentPacking.PackedMatch.Local.Stage DescentResetGates ProtocolRAM
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
variable (fitsStencil : e ≤ laneBits (S.groupWidth k tail age + k) payload
    (S.localWalshBits p (S.groupWidth k tail age + k) f (quota S.rounds)) - k)
  (fitsSigned : e ≤ previous) (fitsCut : previous ≤ S.groupWidth k tail age) (count : Bank)
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

/-- These support proofs refer only to the physical layout constructed for the date.
Changing the starting memory or the accepted graph does not change either operand. -/
structure NamedCodeRoom : Prop where
  prepared : (rc).PreparedFits book
  scene : (v).front.SceneRoom ((v).actorEnd b) ((v).issuedScene b older) w

local notation "room₀" => NamedCodeRoom G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (prevMeta prevArgs : ℕ) (seed : Bool) (archive : PriorRolePages) (s Z : ℕ) (op : RotorSpec)
  (capacity : venue.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256)
  (room : NamedCodeRoom G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count)
local notation "inputs" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prevMeta prevArgs seed room.prepared room.scene
local notation "finish" => FinalInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prevMeta prevArgs seed
  room.prepared room.scene archive s Z op capacity

/-- All computational operands are the actual earlier register, the calendar, and the common primitive alphabet. -/
def namedEntered : DateCode w :=enterCode (a).ingress floor inputs finish io

local notation "compiled" => namedEntered G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  prevMeta prevArgs seed archive s Z op capacity room

theorem namedEntered_issued :
    ∃ (u : (atIngress (a).ingress floor (a) rfl rfl).DateInputs start w) (z : u.FinalInputs),
      HEq inputs u ∧ HEq finish z ∧ compiled=entered (a).ingress floor rfl rfl u z io.hubs
        (fun x=>io.atoms x.val) (fun j=>io.wire j.1.val j.2.val) :=
  enterCode_issued (a).ingress floor rfl rfl
    (named_ingress_bound floor G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io) inputs finish io

/-- An execution on an accepted observation and an execution on any other tape have exactly
the same signed-port scan, root and survivor instructions, clock, and restored role banks. -/
theorem namedEntered_static (other : room₀) :
    compiled=namedEntered G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
      prevMeta prevArgs seed archive s Z op capacity other :=rfl

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
