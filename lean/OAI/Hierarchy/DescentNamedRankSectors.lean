import OAI.Hierarchy.DescentNamedWordGeometry
import OAI.Hierarchy.DescentResetControlCuts
import OAI.Hierarchy.DescentReachedOriginalInputs

namespace OAI
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentResetLocalRoster DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCommonHost DescentFallbackPeriod DescentRecordedRotorLayers DescentSIMDLookup
open DescentDenseHostOrder DescentPackedWalsh DescentPacking.PackedMatch.Local.Stage ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => S.groupWidth k tail i
local notation "r" => (Z).k-(T).commonDepth
local notation "ht" => GroupStage.depthBound D n f g
local notation "L" => 2^(cc+k-(T).commonDepth)
local notation "K" => 2*(A).cap
local notation "units" => originalBits D k n ht (A).cap (programCount ctl.board ht) g
variable {a₀ : PhysicalReset} {out Wd : ℕ} (I : a₀.DateInputs out Wd)
local notation "s" => a₀.successor.sheets
local notation "area" => (a₀.successor.remap (a₀.rebased out)).endAddress

variable (p drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
    (venue : StageVenueTail.Date) (io : Dated.Operands) (floor w : ℕ)
local notation "a" => named G S ctl.board k tail i p f g drift degree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start

local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take i).prod*256
local notation "hostHt" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤ wide-k) (fitsSigned : e≤ previous) (fitsCut : previous≤ cc) (count : Bank)
local notation "sh" => namedStencil G S ctl.board k tail i p f g drift degree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S ctl.board k tail i p f g drift degree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S ctl.board k tail i p f g drift degree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀


local notation "older" => namedOriginals G S ctl.board k tail i p f g drift degree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
    (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
local notation "u" => DateInputs.fromNamed G S ctl.board k tail i p f g drift degree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  previousMeta previousArguments initial prepared scene


/-- Sizes of the three numbered sectors and their rectangular receiving sheet,
including the physical space for every absent receiver. -/
theorem named_rank_sectors (paid : (A).cap=cap) (priorDegree : venue.degree=D) (ready : (u).Ready) :
    (v).receiver.blocks=2^k ∧ (u).sectors.stems=stemsCount B ∧
    (u).sectors.contacts=contactCount B ∧ (u).sectors.privates=privateCount B ∧
    (v).receiver.hosts=(v).sheets.hosts ∧ (v).receiver.groups=S.groupCount (i+1) ∧
    (v).sheets.groups=S.groupCount (i+1) ∧ (v).receiver.lanes=(v).sheets.lanes ∧
    Fintype.card B.next.V≤(v).sheets.hosts ∧ (v).sheets.hosts≤2^w:=by
  subst D
  have counts:=original_donor_domain B paid
  have stems : (u).sectors.stems=stemsCount B:=congrArg (2*·) counts
  have priv : (u).sectors.privates=privateCount B:=by
    have h:=original_private_count B M
    rw [paid] at h
    exact h.symm
  obtain ⟨_,limit,ordered,last⟩:=(v).control_address_bounds base₀
  exact ⟨rfl,stems,congrArg (2*·) (original_choices B).symm,priv,rfl,rfl,rfl,rfl,
    B.next.valid.host,limit.trans (ordered.trans (last.trans ready.full.le))⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
