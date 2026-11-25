import OAI.Hierarchy.DescentScheduledContactRoom
import OAI.Hierarchy.DescentCalendarMixedGeometry
import OAI.Hierarchy.DescentPhysicalResetDateOperands

namespace OAI
/-! # Packed read widths for the four acquired candidate tables -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup
noncomputable section
variable (v : ResetOutput) {payload bw : ℕ}

theorem mixed_read_pitch (aligned : ContactAligned v)
    (tables : ∀t,t∈v.rootUnits ∨ t∈v.receiverUnits → t*v.receiver.lanes≤payload/2)
    (wide : payload≤bw) :
    let a:=v.sheets
    let c:=v.front.contact
    let d:=v.front.donor
    (a.lanes*max (a.metaBits*5) a.metaBits≤bw/2) ∧
    (a.lanes*max (a.metaBits*9) (a.metaBits*7)≤bw/2) ∧
    (c.batch*max (c.fieldBits*c.oldFields) c.viewBits≤bw/2) ∧
    d.batch*max (d.fieldBits*(DescentContactMaskShape.donors d+1)) d.fieldBits≤bw/2:=by
  dsimp only
  let b:=v.sheets.metaBits
  let c:=v.front.contact
  let d:=v.front.donor
  have grant (t : ℕ) (member : t∈v.rootUnits ∨ t∈v.receiverUnits) :
      v.receiver.lanes*t≤bw/2:=by
    rw [Nat.mul_comm];exact (tables _ member).trans (Nat.div_le_div_right wide)
  have rank:=grant (b*5+b*5) (.inr (by simp [receiverUnits,b]))
  have mask:=grant (8*b+b) (.inr (by simp [receiverUnits,b]))
  have matrix:=grant (c.fieldBits*c.oldFields+c.fieldBits) (.inl (by simp [rootUnits,c]))
  have view:=grant (c.viewBits+c.viewBits) (.inl (by simp [rootUnits,c]))
  have count:=grant (d.fieldBits*d.boardFields+d.fieldBits) (.inl (by simp [rootUnits,d]))
  rw [aligned.newLanes,aligned.probeLanes,aligned.donorLanes]
  refine ⟨(Nat.mul_le_mul_left _ (show max (b*5) b≤b*5+b*5 by omega)).trans rank,
    (Nat.mul_le_mul_left _ (show max (b*9) (b*7)≤8*b+b by omega)).trans mask,?_,?_⟩
  · by_cases narrow : c.fieldBits*c.oldFields≤c.viewBits
    · rw [max_eq_right narrow]
      exact (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans view
    · rw [max_eq_left (Nat.le_of_not_ge narrow)]
      exact (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans matrix
  · have bound:=Nat.mul_le_mul_left d.fieldBits (DescentContactMaskShape.donor_arity d)
    apply LE.le.trans (Nat.mul_le_mul_left _ ?_) count
    exact max_le (bound.trans (Nat.le_add_right _ _)) (Nat.le_add_left _ _)

/-- Both halves of every returned sender and its original board fit the purchased pitch. -/
theorem mixed_sender_pitch (aligned : ContactAligned v) (start : ℕ)
    (tables : ∀t,t∈v.rootUnits ∨ t∈v.receiverUnits → t*v.receiver.lanes≤payload/2)
    (wide : payload≤bw) : (v.front.donor.sender start).Packed bw:=by
  let d:=v.front.donor
  let b:=d.fieldBits
  let p:=b*d.laneFields
  have grant (t : ℕ) (member : t∈v.rootUnits) : d.batch*t≤bw/2:=by
    rw [show d.batch=v.receiver.lanes from aligned.donorLanes,Nat.mul_comm]
    exact (tables _ (.inl member)).trans (Nat.div_le_div_right wide)
  have board:=grant (b*d.boardFields+b) (by simp [rootUnits,b,d])
  have split:=grant (p*2+p) (by simp [rootUnits,p,b,d])
  have remote:=grant (b*d.returnFields+b) (by simp [rootUnits,b,d])
  have field : 1≤b:=aligned.inputField
  constructor
  · change 0 < v.front.donor.batch
    rw [aligned.donorLanes]
    exact aligned.lanes
  · change d.batch*max (b*d.boardFields) p≤bw/2
    by_cases leq : b*d.boardFields≤p
    · rw [max_eq_right leq];exact (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)).trans split
    · rw [max_eq_left (Nat.le_of_not_ge leq)]
      exact (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans board
  · change d.batch*max (p*2) b≤bw/2
    by_cases leq : p*2≤b
    · rw [max_eq_right leq];exact (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)).trans board
    · rw [max_eq_left (Nat.le_of_not_ge leq)]
      exact (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans split
  · change d.batch*max (b*d.returnFields) b≤bw/2
    exact (Nat.mul_le_mul_left _ (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))).trans remote
  · change d.laneFields≤2^p
    have leq:=Nat.mul_le_mul_right d.laneFields field
    exact (by simpa [p] using leq : d.laneFields≤p).trans (Nat.lt_two_pow_self.le)


end
end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetNewActorDirectory DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "H" => S.hostSize i
local notation "J" => 2^(T).commonDepth
local notation "r" => (Z).k-(T).commonDepth
local notation "ht" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r ht).card
local notation "gs" => S.groupCount (i+1)
local notation "cap₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(ht+1))
local notation "oldWidth" => DescentPackedPrivateMenu.fieldBits (Z).graph r ht (2^r*(2*(A).cap))
    (DescentRecordedRotorLayers.width f (A).cap) C (Z).width
variable (oldBatch batch : ℕ) (calendar : List ℕ) (paid : (A).cap=(calendar.take i).prod*256)
local notation "cap" => (calendar.take i).prod*256
local notation "field₀" => ResetMiddle.fieldWidth D cap n k ht
local notation "table₀" => CandidateSheets.fromBoard S ctl.board k tail i D f g cap batch
local notation "meta₀" => (table₀).metaBits
local notation "month" => CandidateFront.menu S ctl.board k tail i D f g oldBatch batch C ctl.bitsR calendar
local notation "good" => contactOutputs B H oldBatch field₀ (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) gs (2^k)
    batch (month).contact.outputBits meta₀
local notation "deck" => privateProjection («H»:=H) (field:=oldWidth) B oldBatch batch meta₀
variable {date : PhysicalReset} {floor bw : ℕ} (I : date.DateInputs floor bw)
local notation "v₀" => date.successor
local notation "base₀" => date.rebased floor
local notation "phys₀" => (v₀).front
local notation "peer₀" => (phys₀).peer
local notation "pitch₀" => (phys₀).contactLayout ((v₀).actorEnd base₀)
local notation "Q₀" => (v₀).privateShape
local notation "K₀" => (v₀).contactShape
local notation "don₀" => (phys₀).donorStart ((v₀).actorEnd base₀)
local notation "used" => Fintype.card B.next.V
local notation "rawSize" => H*shelf
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "K" => 2*(A).cap
local notation "F₀" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r

include paid in
/-- The concrete original sender and the current rank/mask renderer use the four
purchased keys at the actual, possibly padded, lane pitch. -/
theorem original_read_pitch (front : (v₀).front=month)
    (aligned : ResetOutput.ContactAligned v₀)
    {payload : ℕ} (tables : ∀t,t∈(v₀).rootUnits ∨ t∈(v₀).receiverUnits →
      t*(v₀).receiver.lanes≤payload/2) (wide : payload≤bw) (markerStart : ℕ) :
    let mark:=(good).donor.markers markerStart shelf (month).peer.bits
    (I.masked.lanes*max (I.masked.field*5) I.masked.field≤bw/2) ∧
    (I.masked.lanes*max (I.masked.field*9) (I.masked.field*7)≤bw/2) ∧
    (oldBatch*max (field₀*mark.oldFields) mark.viewBits≤bw/2) ∧
    oldBatch*max (field₀*(L*(2*(A).cap)+1)) field₀≤bw/2:=by
  have donor : (month).donor = (good).donor := canonical_donor B oldBatch batch field₀ meta₀ calendar paid
  let result:=(v₀).mixed_read_pitch aligned tables wide
  refine ⟨result.1,result.2.1,?_,?_⟩
  · have m:=result.2.2.1
    rw [front] at m
    change oldBatch*max (field₀*((month).donor.markers markerStart shelf (month).peer.bits).oldFields)
      ((month).donor.markers markerStart shelf (month).peer.bits).viewBits≤bw/2 at m
    rw [donor] at m
    exact m
  · have c:=result.2.2.2
    rw [front,donor] at c
    exact c

include paid in
theorem original_sender_pitch (front : (v₀).front=month)
    (aligned : ResetOutput.ContactAligned v₀) {payload : ℕ}
    (tables : ∀t,t∈(v₀).rootUnits ∨ t∈(v₀).receiverUnits → t*(v₀).receiver.lanes≤payload/2)
    (wide : payload≤bw) (start : ℕ) :
    (oldBatch*max (field₀*8) (month).peer.bits≤bw/2) ∧ ((good).donor.sender start).Packed bw:=by
  have donor : (month).donor = (good).donor := canonical_donor B oldBatch batch field₀ meta₀ calendar paid
  have gather:=(v₀).mixed_sender_pitch aligned start tables wide
  rw [front,donor] at gather
  refine ⟨?_,gather⟩
  have root (b : ℕ) (hb : b∈(v₀).rootUnits) : (v₀).front.contact.batch*b≤bw/2:=by
    rw [aligned.probeLanes,Nat.mul_comm]
    exact (tables _ (.inl hb)).trans (Nat.div_le_div_right wide)
  have field:=root _ (show (v₀).front.contact.fieldBits*8+(v₀).front.contact.fieldBits∈(v₀).rootUnits by
    simp [ResetOutput.rootUnits])
  have mark:=root _ (show (v₀).front.peer.bits∈(v₀).rootUnits by simp [ResetOutput.rootUnits])
  rw [front] at field mark
  change oldBatch*(field₀*8+field₀)≤bw/2 at field
  by_cases leq : field₀*8≤(month).peer.bits
  · rw [max_eq_right leq];exact mark
  · rw [max_eq_left (Nat.le_of_not_ge leq)]
    exact (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans field


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
