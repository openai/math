import OAI.Hierarchy.DescentNamedDonorWiring
import OAI.Hierarchy.DescentNamedResetDateInputs
import OAI.Hierarchy.DescentPhysicalOriginalDonorDirectory
import OAI.Hierarchy.DescentReachedOriginalDonorDeck

namespace OAI
/-! Native donor columns in the actual public-number section of a calendar reset. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentPacking.PackedMatch.Local.Stage
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : Dated.Operands) (floor w : ℕ)
local notation "M" => 2^e
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
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
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


local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
    (scene : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
local notation "u" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  previousMeta previousArguments initial prepared scene
local notation "ss" => (v).sheets
local notation "r" => ((v).remap base₀).endAddress
local notation "deck" => (ss).inputDonorsEnd r
local notation "N₀" => 2^k*(2*cap)


local notation "A" => (v).contactShape
local notation "D" => (A).donor
local notation "lo" => (v).front.donorStart early
local notation "end₀" => (v).trunkEnd base₀
local notation "O" => (v).issuedScene base₀ older
local notation "mark" => (D).markers lo (A).shapes (A).markerBits
local notation "oldH" => (D).hosts
local notation "oldG" => (D).groups
local notation "L" => (D).lows
local notation "K" => 2*(D).cap
local notation "field" => (D).fieldBits
local notation "arity" => DescentOldContactSender.count (D).degree L (D).cap (D).n (D).residual
local notation "chart" => (v).actor.directory actorBase
local notation "receiver" => (v).remap base₀
local notation "pre" m:arg => (u).numbered.prefixOutput r ((u).masked.image ((u).privateResult m))
local notation "postTrunk" m:arg => ((v).front.trunkScene early O scene).image m
local notation "src" => (O).donor
local notation "P₀" => (u).numbered.publicSide r
local notation "panels" => (ss).originalDonors
variable (groupShape : oldG=(ss).groups*(ss).blocks)
    (xs : Fin oldH→Fin oldG→Fin arity→Cell field)
    (adj : Fin oldH→Fin (D).degree→Option (Fin oldH))
    (rows : Fin L→Fin K→Fin oldH→Fin oldG→Cell field)
local notation "labelValues" => (A).numberingValues lo board xs adj rows (ss).selectorBits (ss).shortBits groupShape

/-- All five operand and memory-layout identities are fixed by the registered calendar. -/
theorem named_donor_wiring : (u).DonorWiring:=by
  refine ⟨rfl,rfl,?_,rfl,rfl⟩
  change HEq ((A).originalSensorsAt lo end₀ src (L*K)) ((A).originalSensors lo end₀ src)
  rw [(A).originalSensorsAt_full lo end₀ src]

/-- Feed the dated original sender's retained fields directly into the named publisher
and gather through the actual actor count and inverse. -/
theorem named_donor_fields {used : ℕ} (name : Fin used→Fin (v).front.peer.hosts)
    (ok : (u).Ready) (m : Memory w) (values : (panels).Values)
    (seen : (panels).Seen ((A).originalSensors lo end₀ src) values ((u).donorDeckEntry m))
    (countWord : m (chart).count.base=(used:Word w))
    (invWord : ∀i:Fin used,m ((chart).inverse.base+i.val)=((name i).val:Word w))
    (countFits : used<2^w) (hostsFit : (ss).hosts≤2^w) (invSize : used≤(chart).inverse.size) :
    (∀x side j,Source ((P₀).old.label x side j) ((panels).denseLabel (H:=(ss).hosts) name values x side j) M (pre m)) ∧
    (∀x side cargoField j,Source ((P₀).old.cargo x side cargoField j) ((panels).denseCargo (H:=(ss).hosts) name values x side cargoField j) M (pre m)) :=by
  have issued : (panels).Seen (u).numbered.sensor values ((u).donorDeckEntry m):=by
    change (panels).Seen ((A).originalSensorsAt lo end₀ src (L*K)) values ((u).donorDeckEntry m)
    rwa [(A).originalSensorsAt_full lo end₀ src]
  have exhibited:=(panels).exhibits ((ss).inputDonorsBase r) (u).numbered.sensor values ((u).donorDeckEntry m)
    ok.numbers.donor issued
  have directory:=(u).donor_prefix_directory ok m name countWord invWord countFits hostsFit invSize
  exact (panels).dense_sources name values (pre m) ((ss).inputDonorsBase r) (receiver).first
    (chart).count (chart).inverse r directory exhibited

/-- The actual mounted sender and original actor count/inverse are enough to read the
whole dense prior, for both signs and every candidate. -/
theorem named_donor_sources {used : ℕ} (name : Fin used→Fin (v).front.peer.hosts)
    (ok : (u).Ready) (m oldMem : Memory w)
    (before : ((D).sender lo).Before src xs adj rows oldMem)
    (jobs : ((D).sender lo).Packed w)
    (packed : M*max (field*8) (A).markerBits≤w/2)
    (view : M*max (field*(mark).oldFields) (mark).viewBits≤w/2)
    (tailFit : (A).marker end₀+oldH*chunks oldG M<2^w)
    (keys : DescentResetLocalRoster.rootSlots (D).residual (2^(D).n) * (2^(D).n+2^(D).height)<2^field)
    (countWidth : M*max (field*(L*K+1)) field≤w/2)
    (haloWidth : (D).degree+2<2^(D).cargoBits)
    (kept : ∀z,z<(mark).endAddress→(postTrunk m) z=(D).result lo (A).shapes (A).markerBits src board
      scene.donor (ok.donors.trans_lt ok.trunk) packed oldMem z)
    (countWord : m (chart).count.base=(used:Word w))
    (invWord : ∀i:Fin used,m ((chart).inverse.base+i.val)=((name i).val:Word w))
    (countFits : used<2^w) (hostsFit : (ss).hosts≤2^w) (invSize : used≤(chart).inverse.size) :
    (∀x side j,Source ((P₀).old.label x side j) ((panels).denseLabel (H:=(ss).hosts) name labelValues x side j) M (pre m)) ∧
    (∀x side cargoField j,Source ((P₀).old.cargo x side cargoField j) ((panels).denseCargo (H:=(ss).hosts) name labelValues x side cargoField j) M (pre m)) :=by
  have directory:=(u).donor_prefix_directory ok m name countWord invWord countFits hostsFit invSize
  have project:=((A).cuts end₀).2.2.2.2.2.trans_lt ok.mass
  exact (A).issued_original_columns lo end₀ src board scene.donor (ok.donors.trans_lt ok.trunk)
    packed xs adj rows oldMem (postTrunk m) before jobs view ok.donors tailFit keys countWidth haloWidth kept
    (ss).selectorBits (ss).shortBits groupShape name ((u).donorDeckEntry m) ((u).original_donor_frame m ok)
    project ((ss).inputDonorsBase r) (receiver).first r (chart).count (chart).inverse ok.numbers.donor directory

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
