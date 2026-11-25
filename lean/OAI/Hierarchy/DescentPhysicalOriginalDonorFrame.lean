import OAI.Hierarchy.DescentPhysicalOriginalScalarFrame
import OAI.Hierarchy.DescentResetOriginalDonorMemory

namespace OAI
/-! # Earlier signed donor rows remain readable at the authentic numbering clock -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescentSixParty.Chronology
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b₀" => a.rebased floor
local notation "s" => (v).sheets
local notation "r" => ((v).remap b₀).endAddress
local notation "D" => (v).front.donorStart ((v).actorEnd b₀)
local notation "A" => (v).contactShape
local notation "F" => (v).trunkEnd b₀
local notation "O" => (v).issuedScene b₀ u.earlier
local notation "scan" m => ((v).front.trunkScene ((v).actorEnd b₀) O u.sceneFits).image m

def contactShelf (m : Memory w) :=(A).held D F (O).donor (scan m)
def donorDeckEntry (m : Memory w) :=(u.numbered.scalarPhase r w).image (u.coordinateResult m)

theorem original_donor_frame (m : Memory w) (ok : u.Ready) (at_ : ℕ) (key : at_<(A).choicePage F) :
    u.donorDeckEntry m at_=u.contactShelf m at_ :=by
  have bounds:=(A).cuts F
  have high:=key.trans_le (bounds.2.2.2.2.1.trans bounds.2.2.2.2.2)
  have earlier:=high.trans_le ((v).receipt_order b₀).1
  have privateLow:=earlier.trans_le ((v).receipt_order b₀).2
  have mixedLow : at_<(s).metaEnd r:=by rw [←u.masks_end];exact privateLow.trans_le (u.masked.ordered.1.trans u.masked.ordered.2)
  have low : (s).metaEnd r≤(s).coordinateEnd r:=by rw [CandidateSheets.coordinateEnd,(s).stemSources.extent];exact Nat.le_add_right ..
  have prep : (s).coordinateEnd r≤(s).inputDonorsBase r:=by rw [CandidateSheets.inputDonorsBase,DescentResetOriginalZeroHalo.shift];exact Nat.le_add_right ..
  obtain ⟨t,h,z⟩:=(s).originalDonors.cuts ((s).inputDonorsBase r)
  have upper:=(t.trans (h.trans z)).trans_lt ok.numbers.donor.room
  have book:=DescentResetOriginalZeroHalo.any ((s).coordinateEnd r) (s).hosts (s).groups (s).lanes (s).metaBits
    (s).zeroBits (s).shortBits (s).haloBits u.numbered.degree (u.coordinateResult m) upper
  have joint:=(v).joint_any b₀ u.earlier ((A).issuedImage D F (O).donor (scan m)) ok.joints ok.packed
  have fits:=(A).fieldsAt_fits D F (O).donor u.sceneFits.donor ok.donors ok.mass
  have project:=DescentResetStemProjectExpr.any ((A).projected F) (A).sparseHosts (A).groups (A).blocks (A).metaBits
    (A).donor.batch (A).batch ((A).four ((A).fieldsAt D F (O).donor)) (u.contactShelf m)
    ok.projectionLanes ok.projectionBlocks (fun j=>fits _ _) ok.mass
  exact (book.2 at_ (.inl (mixedLow.trans_le low))).trans
    ((u.coordinateResult_frame m ok (prep.trans_lt upper) at_ earlier).trans
      ((joint.2 at_ (.inl high)).trans (project.2.1 at_ (.inl (key.trans_le bounds.2.2.2.2.1)))))

theorem original_donor_retained {H G M width : ℕ} (m : Memory w) (ok : u.Ready) (op : Expr)
    (val : Fin H→Fin G→Cell width) (fit : op.Fits w ((A).choicePage F)) (seen : Source op val M (u.contactShelf m)) :
    Source op val M (u.donorDeckEntry m):=fun p=>
  (eval_below op _ (u.contactShelf m) (u.donorDeckEntry m) fit (u.original_donor_frame m ok)).trans (seen p)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
