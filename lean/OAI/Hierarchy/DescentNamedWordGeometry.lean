import OAI.Hierarchy.DescentOriginalBoardGeometry
import OAI.Hierarchy.DescentNamedScalarLayout
import OAI.Hierarchy.DescentNamedOriginalScalarFit
import OAI.Hierarchy.DescentCalendarOriginalWordRead

namespace OAI
/-! # Calendar dimensions of the four physical original-number passes -/
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

/-- The actual lane counts, signed selector domain, and sector offsets of
the four native writers, expressed in the reached branch's coordinates. -/
structure NumberGeometry : Prop where
  geometry : I.numbered.geometry=publicShape B
  height : I.numbered.treeHeight=ht
  nodes : I.numbered.boardBits=(Z).n
  ports : I.numbered.boardPorts=h
  board : HEq I.numbered.board (Z).graph
  precision : I.numbered.resultBits=units
  funded : 0<(s).metaBits
  zero : 0<(s).zeroBits
  degree : I.numbered.degree=(A).degree
  bits : I.numbered.blockBits=k
  stems : I.numbered.stems=stemsCount B
  contacts : I.sectors.contacts=contactCount B
  stemSlot : ∀j,(I.numbered.stemShelf j).val=j.val
  publicSlot : ∀j,(I.numbered.publicShelf j).val=stemsCount B+j.val
  privateSlot : ∀j,(I.numbered.privateShelf j).val=stemsCount B+1+contactCount B+j.val
  side : ∀j:Fin (stemsCount B),I.numbered.side (j.cast stems.symm)=(stemTag B j).1
  room : (A).degree+1<2^(s).stemBits
  donors : I.numbered.signedSlots=L*K
  request : ∀j,I.numbered.request (j.cast contacts.symm)=donor_query B j
  ticket : ∀c,(Z).senderJoint T false c<2^(s).shortBits
  halo : ∀u c,haloNumber B u ((Z).rootVertex T ((Z).placement.owner false c))+1<2^(s).shortBits
  zeroReg : ∀x,(I.numbered.zero x).Fits Wd ((s).inputDonorsEnd area)
  haloReg : ∀x,(I.numbered.halo x).Fits Wd ((s).inputDonorsEnd area)
  jobs : (s).jobs = (s).blocks * ((s).contacts + (s).privates)

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

set_option maxHeartbeats 900000 in
theorem named_word_geometry (paid : (A).cap=cap) (priorDegree : venue.degree=D) (ready : (u).Ready) :
    NumberGeometry B (u):=by
  subst D
  let N:=2^k*(2*cap)
  let choices:=DescentResetLocalRoster.rootSlots k (2^n)*(2^n+2^(GroupStage.depthBound venue.degree n f g))
  let shapes:=(DescentDenseHostOrder.roster ctl.board k (GroupStage.depthBound venue.degree n f g)).card
  let X:=max choices (max (venue.degree+2) shapes)
  have old:((u).numbered).signedSlots=L*K:=original_donor_domain B paid
  have stemN : (u).numbered.stems=stemsCount B:=congrArg (2*·) old
  have contactsN : (u).sectors.contacts=contactCount B:=congrArg (2*·) (original_choices B).symm
  have widths:=original_short_room B (X:=X)
    (by rw [original_choices B];exact le_max_left ..) ((le_max_left ..).trans (le_max_right ..))
  have scalarFits:=((a).successor).original_scalar_fits base₀ N ready.numbers.donor.room
  refine ⟨original_board_geometry B paid,rfl,B.dimension.symm,rfl,B.graph.symm,?_,?_,by change 0 < 1;decide,
    input.branch.symm,rfl,stemN,contactsN,fun _=>rfl,?_,?_,original_stem_side B paid,?_,old,
    original_donor_request B,widths.1,widths.2,fun x=>scalarFits.1 x.val,fun _=>scalarFits.2.1,rfl⟩
  · change originalBits _ _ _ _ cap _ _=_
    rw [paid]
  · change 0<CandidateFront.endpointWidth venue.degree shapes (2^g*cap)
    exact ((Nat.clog_pos (by decide) (by omega) : 0 < Nat.clog 2 (venue.degree+2)).trans_le
      (Nat.le_add_right _ (Nat.clog 2 (shapes+1)))).trans_le (le_max_right ..)
  · intro j;change 2*N+j.val=stemsCount B+j.val
    exact congrArg (·+j.val) stemN
  · intro j;change 2*N+1+2*choices+j.val=stemsCount B+1+contactCount B+j.val
    exact congrArg₂ (fun n c=>n+1+c+j.val) stemN contactsN
  · rw [input.branch]
    have short : venue.degree+1<2^Nat.clog 2 (2*(venue.degree+1)+2):=
      (by omega : venue.degree+1<2*(venue.degree+1)+2).trans_le (Nat.le_pow_clog (by decide) _)
    exact short.trans_le (Nat.pow_le_pow_right (by decide) ((le_max_right ..).trans (le_max_right ..)))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
