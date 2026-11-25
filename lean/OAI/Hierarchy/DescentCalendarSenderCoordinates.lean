import OAI.Hierarchy.DescentCalendarOriginalSenderRows
import OAI.Hierarchy.DescentNamedResetDateInputs
import OAI.Hierarchy.DescentResetAtlasRoom

namespace OAI
/-! # Coordinates of the named receiver and its original donor operands -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentPackedZip DescentContactOutputShape DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentDenseHostOrder
open DescentResetPeerUnionRAM DescentPackedColony DescentFallbackPeriod DescentSIMDLookup
open DescentContactDonorFront DescentResetLocalRoster ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl) (oldM nextM field metaBits : ℕ) (calendar : List ℕ)
local notation "A" => setupFront S ctl.board k tail i D f g oldM nextM field metaBits C ctl.bitsR calendar
local notation "H" => S.hostSize i
local notation "Ht" => GroupStage.depthBound D n f g
local notation "cap" => (calendar.take i).prod*256
local notation "r" => B.reset.k-B.terminals.commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster B.reset.graph r Ht).card
local notation "bits" => (A).peer.bits
local notation "donor" => peerDonorShape B H oldM field (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3))

private theorem original_donor_heq {v v' : CandidateFront} {start : ℕ}
    (same : v=v') (x : v.Originals start) (y : v'.Originals start) (xy : HEq x y) :
    HEq x.originalDonors y.originalDonors:=by
  subst v'
  cases eq_of_heq xy
  rfl

theorem original_room {a b : CandidateFront} {start w : ℕ}
    (ab : a=b) (x : a.Originals start) (y : b.Originals start) (xy : HEq x y) (flags count inverse : Bank)
    (room : a.SceneRoom start (a.fromOriginals start x flags count inverse) w) :
    b.SceneRoom start (b.fromOriginals start y flags count inverse) w:=by
  subst b
  cases eq_of_heq xy
  exact room

private theorem original_trunk {a b : CandidateFront} {start w : ℕ}
    (ab : a=b) (x : a.Originals start) (y : b.Originals start) (xy : HEq x y) (flags count inverse : Bank)
    (room : a.SceneRoom start (a.fromOriginals start x flags count inverse) w) (m : Memory w) :
    (a.trunkScene start (a.fromOriginals start x flags count inverse) room).image m=
      (b.trunkScene start (b.fromOriginals start y flags count inverse)
        (original_room ab x y xy flags count inverse room)).image m:=by
  subst b
  cases eq_of_heq xy
  rfl

private theorem move_heq {a b : DescentContactDonorFront.Shape} (eqn : a=b) (u : a.Input) :
    HEq (DescentContactDonorFront.Shape.move eqn u) u:=by cases eqn;rfl

variable (paid : input.placement.cap=cap) (v : ResetOutput) (base : ℕ)
    (old : EarlierBanks D k cap n)
local notation "start₀" => v.actorEnd base
local notation "next₀" => (A).oldKeys start₀
local notation "L₀" => peerLayout B next₀ H oldM (A).privateBits ((A).stemField+2) bits
local notation "lo₀" => (L₀).endAddress
local notation "markers₀" => (donor).markers lo₀ shelf bits
local notation "chart" => contactOutputs B H oldM field (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3))
  (S.groupCount (i+1)) (2^k) nextM bits metaBits
local notation "eqShape" => canonical_donor B oldM nextM field metaBits calendar paid
local notation "originals" => calendarOriginals S ctl.board k tail i D f g oldM nextM field metaBits C ctl.bitsR
  calendar start₀ old
variable (front : v.front=(A)) (deck : v.contactShape=chart)

include front in
/-- The donor and the marker end coincide with the raw-table and marker boundaries
of the very same peer pass. The receiver only transports the original donor's type. -/
theorem named_sender_coordinates (src : v.OriginalOperands base) (actual : HEq src originals) :
    v.front.donorStart start₀=lo₀ ∧ v.front.peers start₀=(markers₀).endAddress ∧
      cast (congrArg DescentContactOutputShape.Shape.donorPrior deck) (v.issuedScene base src).donor=
        DescentContactDonorFront.Shape.move eqShape old.donor:=by
  refine ⟨(congrArg (fun p : CandidateFront=>p.donorStart start₀) front).trans
    (canonical_raw_end B oldM nextM field metaBits calendar start₀),?_,?_⟩
  · exact (congrArg (fun p : CandidateFront=>p.peers start₀) front).trans
      (congrArg DescentContactPreROM.Layout.endAddress
        (canonical_contact_layout B oldM nextM field metaBits calendar paid start₀))
  · have same : HEq (v.issuedScene base src).donor old.donor:=original_donor_heq front src originals actual
    exact eq_of_heq ((cast_heq _ _).trans (same.trans (move_heq eqShape old.donor).symm))

/-- The true `EarlierBanks.fromRoot` is one possible donor bank. Casting its
whole original record fixes the source independently of the chosen equality proofs. -/
theorem calendar_original_operands :
    HEq (cast (congrArg (fun p : CandidateFront=>p.Originals start₀) front.symm) originals) originals:=
  cast_heq _ _


local notation "dir" => v.actor.directory (v.middle.stop base)
local notation "moved" => DescentContactDonorFront.Shape.move eqShape old.donor
local notation "scene₁" => (A).fromOriginals start₀ originals (dir).flags (dir).count (dir).inverse
local notation "trueEnd" => (A).trunkEnd start₀
/-- The physical original sender rows discharge the four-source part of the
receiver capture. Both statements read the identical post-trunk memory. -/
theorem named_sender_reads {w : ℕ} (src : v.OriginalOperands base) (actual : HEq src originals)
    (room : v.front.SceneRoom start₀ (v.issuedScene base src) w) (m : Memory w)
    (values : (chart).senderRegisters)
    (observed : ∀q j,DescentPackedZip.Source ((chart).fieldsAt lo₀ trueEnd moved q j) (values q j) oldM
      ((chart).held lo₀ trueEnd moved (((A).trunkScene start₀ scene₁
        (original_room front src originals actual (dir).flags (dir).count (dir).inverse room)).image m))) :
    ∀q j,DescentPackedZip.Source (v.contactShape.fieldsAt (v.front.donorStart start₀) (v.trunkEnd base)
      (v.issuedScene base src).donor q j) (cast (congrArg DescentContactOutputShape.Shape.senderRegisters deck.symm) values q j)
      v.contactShape.donor.batch
      (v.contactShape.held (v.front.donorStart start₀) (v.trunkEnd base) (v.issuedScene base src).donor
        ((v.front.trunkScene start₀ (v.issuedScene base src) room).image m)):=by
  apply DescentContactOutputShape.Shape.reads_cast deck (v.front.donorStart start₀) (v.trunkEnd base)
    (v.issuedScene base src).donor values ((v.front.trunkScene start₀ (v.issuedScene base src) room).image m)
  obtain ⟨place,_,operand⟩:=named_sender_coordinates B oldM nextM field metaBits calendar paid v base old front deck src actual
  have roof : v.trunkEnd base=trueEnd:=congrArg (fun a : CandidateFront=>a.trunkEnd start₀) front
  have same:=original_trunk front src originals actual (dir).flags (dir).count (dir).inverse room m
  change ((v.front.trunkScene start₀ (v.issuedScene base src) room).image m)=_ at same
  rw [place,roof]
  let readRows (donorInputs : (chart).donorPrior) (trunkMemory : Memory w) : Prop :=
    ∀q j, Source ((chart).fieldsAt lo₀ trueEnd donorInputs q j) (values q j) oldM
      ((chart).held lo₀ trueEnd donorInputs trunkMemory)
  exact (congrArg₂ readRows operand same).mpr observed

end
end Hierarchy.DescentSixParty.ClosedReset.Window

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
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


open DescentPackedColony DescentFallbackPeriod.Projected DescentPacking.PackedMatch.Local.Stage
local notation "pop" => S.hostSize age
local notation "rows" => pop*chunks (2^cc) (2^e)
local notation "dir" => (v).actor.directory actorBase
local notation "active" => (v).actor.scene actorBase
local notation "src" => atlasSender atlas sh start count io.hubs g (2^n) roots w
local notation "raw" => CandidateFront.EarlierBanks.fromRoot rc book src (atlas).hostIndex io.hubs dir active
local notation "rfield" => ResetMiddle.fieldWidth venue.degree cap n k Ht
local notation "F₀" => (v).front
local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "scene" => (v).issuedScene base₀ older

/-- The original receiver operands come from its installed root inputs and the
actor directory computed earlier in the same reset date. -/
def namedSenderBanks : CandidateFront.EarlierBanks venue.degree k cap n:=by
  have half : (a).c/2=cap:=by change (2*cap)/2=cap;omega
  exact cast (congrArg (fun t=>CandidateFront.EarlierBanks venue.degree k t n) half) raw

local notation "prior" => namedSenderBanks G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "source" => CandidateFront.calendarOriginals S board k tail age venue.degree f g (2^e) M
  rfield (F₀).metaBits C packet cal early prior
local notation "issued" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count

theorem fromNamed_sender_banks (previousMeta previousArguments : ℕ) (initial : Bool)
    (prepared : (rc).PreparedFits book) (access : (F₀).SceneRoom early scene w) :
    HEq (issued previousMeta previousArguments initial prepared access).earlier source:=HEq.rfl

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
