import OAI.Hierarchy.DescentDatedPhysicalOrdinary
import OAI.Hierarchy.DescentPackedProfileRepack
import OAI.Hierarchy.DescentPackedProfileInstall
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # Installing the retained ordinary profile at the actual matcher's raw input bank -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open ProtocolRAM DescentPackedProfileInstall DescentPackedProfileArchive DescentTerminalEpochChart
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (origin shelf w : ℕ)

/-- The original shelf precedes the overlap workspace. The matcher follows the widening dictionary. -/
def archivePhase : NativePhase w :=
  let p := v.profileRepack
  let src := sourceBank shelf p.seats p.oldLanes
  let dst := (v.area.matcher v.old (p.endAddress origin)).raw
  let digit := v.area.shapeAt.digit
  ⟨DescentPackedProfileRepack.program origin p.seats p.oldLanes p.newLanes p.bits digit src dst w,
   DescentPackedProfileRepack.ticks origin p.seats p.oldLanes p.newLanes p.bits src dst,
   @DescentPackedProfileRepack.image origin p.seats p.oldLanes p.newLanes p.bits digit src dst w,
   DescentPackedProfileRepack.cheap origin p.seats p.oldLanes p.newLanes p.bits digit src dst w⟩

/-- The work interval precedes the first raw input cell, and the bank ends inside the matcher. -/
theorem archive_geometry : v.profileRepack.endAddress origin ≤
      (v.area.matcher v.old (v.profileRepack.endAddress origin)).raw.base ∧
    (v.area.matcher v.old (v.profileRepack.endAddress origin)).raw.base +
      (v.area.matcher v.old (v.profileRepack.endAddress origin)).raw.size ≤
      (v.area.matcher v.old (v.profileRepack.endAddress origin)).endAddr := by
  have before:=v.area.matcherAt_add v.old 0 (v.profileRepack.endAddress origin)
  rw [Nat.add_zero] at before
  dsimp only [DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary.matcher,
    DescentPacking.PackedMatch.Local.Gather.ROM.place,DescentPacking.PackedMatch.Local.Gather.ROM.column,
    DescentPacking.PackedMatch.Local.Gather.ROM.stop]
  constructor
  · rw [before]
    exact (((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans
      (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  · omega

variable (m : Memory w)
    (earlier : (sourceBank shelf v.profileRepack.seats v.profileRepack.oldLanes).Fits w origin)
    (apart : v.profileRepack.endAddress origin ≤
      (v.area.matcher v.old (v.profileRepack.endAddress origin)).raw.base)
    (room : (v.area.matcher v.old (v.profileRepack.endAddress origin)).raw.base +
      (v.area.matcher v.old (v.profileRepack.endAddress origin)).raw.size < 2^w)
include earlier apart room in
theorem archivePhase_runs : (v.archivePhase origin shelf w).Runs m := by
  intro P R K machine
  exact (DescentPackedProfileRepack.any origin v.profileRepack.seats v.profileRepack.oldLanes
    v.profileRepack.newLanes v.profileRepack.bits v.area.shapeAt.digit
    (sourceBank shelf v.profileRepack.seats v.profileRepack.oldLanes)
    (v.area.matcher v.old (v.profileRepack.endAddress origin)).raw
    m earlier apart room).1 machine

include earlier apart room in
theorem archivePhase_frame (addr : ℕ) (scratch : addr<origin ∨ v.profileRepack.endAddress origin≤addr)
    (destination : addr < (v.area.matcher v.old (v.profileRepack.endAddress origin)).raw.base ∨
      (v.area.matcher v.old (v.profileRepack.endAddress origin)).raw.base +
        (v.area.matcher v.old (v.profileRepack.endAddress origin)).raw.size ≤ addr) :
    (v.archivePhase origin shelf w).image m addr = m addr :=
  (DescentPackedProfileRepack.any origin v.profileRepack.seats v.profileRepack.oldLanes
    v.profileRepack.newLanes v.profileRepack.bits v.area.shapeAt.digit
    (sourceBank shelf v.profileRepack.seats v.profileRepack.oldLanes)
    (v.area.matcher v.old (v.profileRepack.endAddress origin)).raw
    m earlier apart room).2.1 addr scratch destination

include earlier apart room in
theorem archivePhase_issued {Pin : Type} (entry : Source Pin) (z : Pin→Bool)
    (seats : v.profileRepack.seats=entry.seats) (bits : v.profileRepack.bits=DescentTerminalEpochBits.width entry.C)
    (pitch : v.profileRepack.newLanes=v.area.lanesAt*v.area.shapeAt.pairs)
    (oldPos : 0<v.profileRepack.oldLanes) (newPos : 0<v.profileRepack.newLanes)
    (extend : DescentTerminalEpochBits.width entry.C≤v.area.shapeAt.digit)
    (observed : ∀j : Fin (DescentPackedProfileTape.slots entry.seats v.profileRepack.oldLanes),
      m (shelf+j.val)=((DescentPackedProfileTape.packed entry.pin z v.profileRepack.oldLanes j.val).val:Word w)) :
    Stored entry v.area.shapeAt.digit (v.area.lanesAt*v.area.shapeAt.pairs) extend
      (v.area.matcher v.old (v.profileRepack.endAddress origin)).raw z ((v.archivePhase origin shelf w).image m) := by
  rw [←pitch]
  let bank:=(sourceBank shelf v.profileRepack.seats v.profileRepack.oldLanes)
  have cap : DescentPackedProfileTape.slots entry.seats v.profileRepack.oldLanes≤bank.size := by
    rw [←seats]
    exact Nat.le_pow_clog (by decide) _
  have low := DescentPackedProfileRepack.issued origin v.profileRepack.oldLanes v.profileRepack.newLanes
    v.area.shapeAt.digit bank (v.area.matcher v.old (v.profileRepack.endAddress origin)).raw
    entry z extend m oldPos newPos earlier cap observed
    (by rw [←seats,←bits]; exact apart) room
  simpa only [archivePhase,←seats,←bits] using low


end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
