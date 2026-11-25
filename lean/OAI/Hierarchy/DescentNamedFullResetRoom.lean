import OAI.Hierarchy.DescentCalendarPhysicalResetRoom
import OAI.Hierarchy.DescentNamedFinalInputs
import OAI.Hierarchy.DescentFundedPreviousBank

namespace OAI
/-! # Native room of the original eight-stage reset emitter and its predecessor archive -/
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

local notation "emit" pr:arg sc:arg => FinalInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prevMeta prevArgs seed pr sc


/-- Incoming stock is the original issued page at every commodity. The seed and
both possible previous date kinds supply the previous primitive archive. -/
private theorem room_of_banks (prepared : (rc).PreparedFits book)
  (scene : (v).front.SceneRoom ((v).actorEnd b) ((v).issuedScene b older) w)
    (archive : PriorRolePages) (seedWidth grain : ℕ) (op : RotorSpec)
    (capacity : venue.cap=cap) (shape₀ : (a).RootShape) (ready : (inputs prepared scene).Ready)
    (hosts : venue.hosts=S.hostSize age) (blocks : venue.k=k)
    (groups : S.baseGroups=2^tail) (radix : S.radix=2^k) (within_ : age<S.length) (positive : 0<M)
    (pages : ∀x,(DescentFundedCensus.priorBank io x).Fits w floor)
    (columns : (v).roleTransfer.transfer.blocks≤archive.blocks)
    (earlier : archive.endAddress≤floor) (ceiling : (a).fullEnd floor<2^w) :
    ((emit prepared scene) archive seedWidth grain op capacity).Room:=by
  let z:=(emit prepared scene) archive seedWidth grain op capacity
  have ingress:=(a).ingress.order floor
  have lo:floor≤ start:=ingress.1.trans (ingress.2.1.trans ingress.2.2)
  obtain ⟨ad,da,dt,tm,mj,jp,pm,mf,fr⟩:=ready.ordered
  have final_:=date_operand_end (a) start
  have cap_: (a).endAddress start<2^w:=ceiling
  have space:start<2^w:=by omega
  have atoms (j) : (z.earlier j).Fits w start:=by
    have ok:=pages j.val
    exact ⟨ok.1,ok.2.1,ok.2.2.trans lo⟩
  have roleFit:=FinalInputs.fromNamed_role_room G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prevMeta prevArgs seed prepared scene
    archive seedWidth grain op capacity columns (earlier.trans lo) space
  exact named_final_room G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor z shape₀ ready hosts blocks groups radix within_ positive rfl atoms roleFit ceiling

theorem FinalInputs.fromNamed_original_room (prepared : (rc).PreparedFits book)
  (scene : (v).front.SceneRoom ((v).actorEnd b) ((v).issuedScene b older) w)
    (archive : PriorRolePages) (seedWidth grain : ℕ) (op : RotorSpec)
    (capacity : venue.cap=cap) (shape₀ : (a).RootShape) (ready : (inputs prepared scene).Ready)
    (hosts : venue.hosts=S.hostSize age) (blocks : venue.k=k)
    (groups : S.baseGroups=2^tail) (radix : S.radix=2^k) (within_ : age<S.length) (positive : 0<M)
    (recorded : DescentFundedCensus.IssuedBanks io venue.hosts venue.groups venue.lanes)
    (previousFits : ∀x,(io.atoms x).Fits w floor)
    (columns : (v).roleTransfer.transfer.blocks≤archive.blocks)
    (earlier : archive.endAddress≤floor) (ceiling : (a).fullEnd floor<2^w) :
    ((emit prepared scene) archive seedWidth grain op capacity).Room:=by
  apply room_of_banks G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prevMeta prevArgs seed prepared scene
    archive seedWidth grain op capacity shape₀ ready hosts blocks groups radix within_ positive _ columns earlier ceiling
  intro x
  have ok:=previousFits x
  rw [recorded.row x] at ok
  exact ok.1

/-- The actual preceding stage supplies the entire old stock ledger and its bounds
on the same memory. No separate operand-bank layout is needed for this run. -/
theorem FinalInputs.fromNamed_reached_room (prepared : (rc).PreparedFits book)
  (scene : (v).front.SceneRoom ((v).actorEnd b) ((v).issuedScene b older) w)
    (archive : PriorRolePages) (seedWidth grain : ℕ) (op : RotorSpec)
    (capacity : venue.cap=cap) (shape₀ : (a).RootShape) (ready : (inputs prepared scene).Ready)
    (hosts : venue.hosts=S.hostSize age) (blocks : venue.k=k)
    (groups : S.baseGroups=2^tail) (radix : S.radix=2^k) (within_ : age<S.length) (positive : 0<M)
    {P : Type} {δ : ℕ} {bits : P→ℕ} {W : MarkedWorld F δ P bits} {q ε : ℝ} {z D wire hist H lanes paid : ℕ}
    (prior : Reached W G q ε S k age z D wire hist) (wide : Fintype.card prior.V≤H)
    (peers : Fin H→Fin D→Option (Fin H)) (mem : Computability.VPVNP.BurstRAM.Memory w)
    (seen : stageVenue prior wide io lanes paid floor peers mem)
    (columns : (v).roleTransfer.transfer.blocks≤archive.blocks)
    (earlier : archive.endAddress≤floor) (ceiling : (a).fullEnd floor<2^w) :
    ((emit prepared scene) archive seedWidth grain op capacity).Room:=by
  obtain ⟨_,_,_,_,hub,_,_,stock,_⟩:=seen
  apply room_of_banks G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prevMeta prevArgs seed prepared scene
    archive seedWidth grain op capacity shape₀ ready hosts blocks groups radix within_ positive _ columns earlier ceiling
  exact fun x=>DescentFundedCensus.priorBank_fits io x hub (stock x)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
