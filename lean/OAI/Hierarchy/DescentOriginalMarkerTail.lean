import OAI.Hierarchy.DescentResetMixedReadPitch
import OAI.Hierarchy.DescentOriginalDonorWordWidths

namespace OAI
/-! # The original marker window is covered by the physical contact projection. -/
namespace Hierarchy.DescentResetStemProject
open DescentSIMDLookup
theorem gather_span (base N H G X a A M : ℕ) :
    base+N*(H*chunks (G*X) A)≤endAddress base N H G X a A M := by
  obtain ⟨copied,packed,_,unpacked,finished⟩:=regions (N:=N) base H G X a A M
  have converted : (converted base N H G X a A M).base≤reshapeBase base N H G X a A M:=Nat.le_add_right ..
  exact (((copied.trans packed).trans converted).trans unpacked).trans
    ((Nat.le_add_right _ _).trans finished)
end Hierarchy.DescentResetStemProject

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

/-- The projection's gather holds at least one full old donor block for each
original host. Its emitted interval bounds every row address used by the old
marker while compiling the four reset measures. -/
theorem original_marker_tail (cal : MixedGeometry B oldBatch batch calendar v₀ base₀) (ok : I.Ready) :
    (good).marker ((v₀).trunkEnd base₀)+H*chunks J oldBatch < 2^bw := by
  let obj:=good
  let first:=(v₀).trunkEnd base₀
  let project:=obj.projected first
  have groups : gs*2^k=J:=by
    rw [B.commonDepth,S.group_cut B.age,pow_add,S.group_power ctl.base ctl.radix]
  have palette : 0 < shelf:=palette_nonempty (Z).graph r ht
  have sparse : H ≤ obj.sparseHosts :=by
    change H ≤ H*shelf
    exact Nat.le_mul_of_pos_right _ palette
  have cols : 0 < obj.fields:=by
    change 0 < (2*((2^(r+1)+2^(r+1)*(2^(Z).n+1))*(2^(Z).n+2^ht)))*4
    positivity
  have slots : H*chunks J oldBatch ≤ obj.fields*(obj.sparseHosts*chunks (obj.groups*obj.blocks) obj.donor.batch):=by
    change H*chunks J oldBatch ≤ obj.fields*(obj.sparseHosts*chunks (gs*2^k) oldBatch)
    rw [groups]
    exact (Nat.mul_le_mul_right _ sparse).trans (Nat.le_mul_of_pos_left _ cols)
  have cuts:=obj.cuts first
  have left : obj.marker first ≤ project:=((cuts.2.1.trans cuts.2.2.1).trans cuts.2.2.2.1).trans cuts.2.2.2.2.1
  have gather:=DescentResetStemProject.gather_span project obj.fields obj.sparseHosts obj.groups obj.blocks
    obj.metaBits obj.donor.batch obj.batch
  have issued : obj.endAddress first=(v₀).massEnd base₀:=by
    change (good).endAddress first=(v₀).contactShape.endAddress first
    rw [cal.contactDeck]
  exact ((Nat.add_le_add left slots).trans gather).trans_lt (issued.le.trans_lt ok.mass)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
