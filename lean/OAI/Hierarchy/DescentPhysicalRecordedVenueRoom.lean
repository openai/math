import OAI.Hierarchy.DescentReachedSheetBounds
import OAI.Hierarchy.DescentPhysicalResetDate
import OAI.Hierarchy.DescentNamedResetVenue

namespace OAI
/-! # The physical reset successor only consumes the directory, census and signed rows at their earlier addresses -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentSIMDLookup DescentDyadicSpan ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {a:PhysicalReset}{floor w:ℕ}(u:a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "book" => (v).receiver
local notation "fund" => (v).fundedEnd b
local notation "src" => FinalInputs.predecessor u

theorem DateInputs.receiver_page {base:ℕ}(limit:(book).rendered ((v).fieldsEnd b)≤base)(space:base<2^w)
    (x:Fin (book).blocks)(j:Fin (2*(book).capacity)):
    ((src).signed x.val j.val).Fits w base ∧ (book).hosts*chunks (book).groups (book).lanes≤((src).signed x.val j.val).size:=by
  let n:=(book).hosts*chunks (book).groups (book).lanes
  let entry:=DescentNextSignedWindow.Native.All.outputBase ((v).fieldsEnd b) (book).capacity (book).signedBits (book).lanes
  let q:=x.val*(2*(book).capacity)+j.val
  have index:q<(book).blocks*(2*(book).capacity):=by
    have small: x.val*(2*(book).capacity)+j.val < (x.val+1)*(2*(book).capacity):=by
      exact (Nat.add_lt_add_left j.isLt _).trans_eq (Nat.succ_mul x.val (2*(book).capacity)).symm
    exact small.trans_le (Nat.mul_le_mul_right _ x.isLt)
  have early:entry+q*span n+span n≤base:=by
    rw [Nat.add_assoc,←Nat.succ_mul]
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ index) _).trans limit
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (early.trans_lt space),early⟩,span_ge n⟩

/-- The caller's earlier inputs are the actor scene, its real inverse/count and raw
    three-column peer output. The signed addresses are derived from the receiver's
    own printed public output. This works before evaluating a single candidate. -/
theorem DateInputs.venue_banks (old:StageVenueTail.Date)(matcher:ℕ)
    (selected:(v).venue=ResetVenue.collect old (v).venue.census (v).actor (book) matcher)
    (blocks:(book).blocks=2^old.k)
    (joined:(book).groups*(book).blocks=(v).venue.census.groups)(positive:0<(book).lanes)
    (scene:(src).actor.Fits w fund)
    (sceneRows:(v).venue.census.jobs*(v).venue.census.hosts*chunks (v).venue.census.groups (v).actor.lanes≤(src).actor.size)
    (earlier:DescentCompactVenuePeers.Room (src).ranks fund w)
    (done_:(book).rendered ((v).fieldsEnd b)≤fund)
    (ceiling:(v).venue.endAddress fund<2^w):
    (v).venue.RunRoom (src) fund 0 w:=by
  let V:=ResetVenue.collect old (v).venue.census (v).actor (book) matcher
  have declared:(v).venue=V:=selected
  have roof:V.endAddress fund<2^w:=declared ▸ ceiling
  have span_:fund≤V.venueStart fund:=(V.after fund).1.trans (V.after fund).2.1
  have top:V.venueStart fund<2^w:=(V.after fund).2.2.trans_lt roof
  rw [declared]
  apply V.run_room (src) fund blocks rfl rfl rfl rfl rfl positive
  · change (v).venue.census.jobs*(v).venue.census.hosts*chunks ((book).groups*(book).blocks) (v).venue.census.lanes ≤
      (v).venue.census.jobs*((v).venue.census.hosts*chunks (v).venue.census.groups (v).venue.census.lanes)
    rw [joined,Nat.mul_assoc]
  · exact scene
  · simpa only [V,ResetVenue.collect,joined] using sceneRows
  · exact earlier
  · intro x j
    exact u.receiver_page (done_.trans span_) top (x.cast blocks.symm) j
  · exact roof

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
