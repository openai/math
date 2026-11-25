import OAI.Hierarchy.DescentPhysicalOriginalScalarFrame

namespace OAI
/-! # Coordinate and trunk reads at the entry to the physical stem-number pass -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSixParty.Chronology DescentSIMDLookup DescentPackedZip ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "s" => (v).sheets
local notation "r" => ((v).remap b).endAddress
local notation "machine" => u.numbered.publicSide r
local notation "mid" m => u.masked.image (u.privateResult m)
local notation "publicOut" m => (machine).dst (u.numbered.prefixOutput r (mid m))

/-- The original public phase, donor numbering and shared scalar dictionary
preserve every address below the end of the six-field coordinate output. -/
theorem public_original_frame (ok : u.Ready) (m : Memory w) (z : ℕ) (hz : z < (s).coordinateEnd r) :
    (publicOut m) z=u.coordinateResult m z := by
  have deck : (s).coordinateEnd r≤(s).inputDonorsBase r := by
    rw [CandidateSheets.inputDonorsBase,DescentResetOriginalZeroHalo.shift]
    exact Nat.le_add_right ..
  obtain ⟨l,h,t⟩ := (s).originalDonors.cuts ((s).inputDonorsBase r)
  have donors : (s).inputDonorsBase r≤(s).inputDonorsEnd r:=l.trans (h.trans t)
  let co:=u.coordinateResult m
  let scalar:=(u.numbered.scalarPhase r w).image co
  have held:=DescentResetOriginalZeroHalo.any ((s).coordinateEnd r) (s).hosts (s).groups (s).lanes
    (s).metaBits (s).zeroBits (s).shortBits (s).haloBits u.numbered.degree co
    (donors.trans_lt ok.numbers.donor.room)
  have gathered:=(s).originalDonors.any ((s).inputDonorsBase r) u.numbered.sensor ok.numbers.donor scalar
  have pub:=(machine).any ok.numbers.public_ (u.numbered.prefixOutput r (mid m))
  exact (pub.2.2 z (.inl (hz.trans_le (deck.trans donors)))).trans
    ((gathered.2.2 z (.inl (hz.trans_le deck))).trans (held.2 z (.inl hz)))

/-- The public and private numberers preserve the measured trunk, including
the parent directory produced after the actors. -/
theorem public_original_scene (ok : u.Ready) (m : Memory w) (z : ℕ) (hz : z < (v).trunkEnd b) :
    (publicOut m) z=((v).front.trunkScene ((v).actorEnd b) ((v).issuedScene b u.earlier) u.sceneFits).image m z := by
  let trunk:=((v).front.trunkScene ((v).actorEnd b) ((v).issuedScene b u.earlier) u.sceneFits).image m
  let old:=(v).issuedScene b u.earlier
  let donor:=(v).front.donorStart ((v).actorEnd b)
  let pub:=(v).contactShape.issuedImage donor ((v).trunkEnd b) old.donor trunk
  have beforeMass:=hz.trans_le ok.ordered.2.2.2.1
  have beforeJoint:=beforeMass.trans_le ((v).receipt_order b).1
  have beforePrivate:=beforeJoint.trans_le ((v).receipt_order b).2
  have «meta» : z<(s).metaEnd r := by
    rw [←u.masks_end]
    exact beforePrivate.trans_le (u.masked.ordered.1.trans u.masked.ordered.2)
  have coord : (s).metaEnd r≤(s).coordinateEnd r := by
    rw [CandidateSheets.coordinateEnd,(s).stemSources.extent]
    exact Nat.le_add_right ..
  have deck : (s).coordinateEnd r≤(s).inputDonorsEnd r := by
    rw [(s).donors_shift]
    omega
  have joint:=(v).joint_any b u.earlier pub ok.joints ok.packed
  have mass:=(v).contactShape.actual donor ((v).trunkEnd b) old.donor u.sceneFits.donor ok.donors
    ok.mass ok.projectionLanes ok.projectionBlocks trunk
  exact (u.public_original_frame ok m z («meta».trans_le coord)).trans
    ((u.coordinateResult_frame m ok (deck.trans_lt ok.numbers.donor.room) z beforeJoint).trans
      ((joint.2 z (.inl beforeMass)).trans (mass.2.2 z (.inl hz))))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
