import OAI.Hierarchy.DescentNamedResetPrefix
import OAI.Hierarchy.DescentNamedResetRootPagesFit
import OAI.Hierarchy.DescentResetAtlasRoom

namespace OAI
/-! # Support for the literal chosen reset root program from its incoming registered venue -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentColonies DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀
/-- The saved word, signed rows, rotor and fallback shelves, and lookup tables
are all addressable within the public reset date. -/
theorem named_prepared_and_sender (pitch : M=2^e)
    (groups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (priorWire : ∀(x:Block k)(j:Fin (2*cap)),(io.wire x.val j.val).Fits w floor ∧
      S.hostSize age*chunks (S.groupCount age) (2^previous)≤(io.wire x.val j.val).size)
    (selected : ∀t∈(v).rootUnits,t*(v).receiver.lanes≤payload/2) (word : payload≤w)
    (ceiling : (a).fullEnd floor<2^w) (stencil : (P).Room w) (spectrum : (E).Fits w) :
    (rc).PreparedFits book ∧
      (atlasSender atlas sh start count io.hubs g (2^n) roots w).OperandRoom (v).middle.signedHosts
        (2^(P).S.c) (v).middle.signedLanes w ((rc).headerEnd book) :=by
  have earlier : ∀t∈(v).rootUnits,t*2^e≤w/2:=by
    intro t ht
    have bound:=selected t ht
    change t*M≤_ at bound
    rw [pitch] at bound
    exact bound.trans (Nat.div_le_div_right word)
  have prior:=named_prefix G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w sh count fitsSigned fitsCut groups radix priorWire earlier ceiling
  obtain ⟨last,packed⟩:=named_root_pages_fit G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count pitch selected word ceiling
  exact atlas_geometry atlas sh start count io.hubs g (2^n) roots stencil spectrum prior last
    rfl rfl rfl rfl rfl packed

theorem named_prepared_room (pitch : M=2^e)
    (groups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (priorWire : ∀(x:Block k)(j:Fin (2*cap)),(io.wire x.val j.val).Fits w floor ∧
      S.hostSize age*chunks (S.groupCount age) (2^previous)≤(io.wire x.val j.val).size)
    (selected : ∀t∈(v).rootUnits,t*(v).receiver.lanes≤payload/2) (word : payload≤w)
    (ceiling : (a).fullEnd floor<2^w) (stencil : (P).Room w) (spectrum : (E).Fits w) :
    (rc).PreparedFits book :=
  (named_prepared_and_sender G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count pitch groups radix
    priorWire selected word ceiling stencil spectrum).1

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
