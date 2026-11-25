import OAI.Hierarchy.DescentProfileRepackTariff
import OAI.Hierarchy.DescentDonorMatcherSpace

namespace OAI
/-! # The genuine matcher raw allocation and common-pitch input cost at a chosen date -/
namespace Hierarchy.DescentSixParty.Chronology.DonorDate
open DescentCompiler DescentSIMDLookup DescentPacking.PackedMatch DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentTerminalEpochChart
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable (d : DonorDate) (payload seats board w factor : ℕ) (old src : Bank) (base floor : ℕ)
local notation "a" => d.schedule payload seats board
local notation "m" => (a).lanesAt
local notation "s" => d.matcher
local notation "b" => DescentTerminalEpochBits.width d.colors
local notation "A" => DescentPackedEpochShelves.grain (payload/2) d.colors
local notation "B" => (m)*(s).pairs
local notation "dst" => ((a).matcher old floor).raw

theorem raw_pitch_bill (cap : 0<d.cap) (boardFits : board≤2^d.exponent)
    (large : 64≤payload) (oldFit : 2*DescentPackedEpochShelves.unit d.colors≤payload/2)
    (wide : 2*d.amount≤payload) (pages : 2^(payload/2)≤d.hosts) (word : w≤factor*payload) :
    (DescentPackedProfileRepack.ticks base seats A B b src dst+
      7*DescentStaticWordColumn.names (DescentPackedProfileRepack.program base seats A B b (s).digit src dst w))*w≤
      131072*factor*(d.hosts*payload+seats*(DescentPackedEpochShelves.unit d.colors+d.amount)) := by
  have matchedRoom := (d.matcher_widths board cap boardFits).2.2.2.1
  have matchWord : (s).digit*(s).pairs≤d.amount := by
    have env : ProfileTable.envelope s≤d.amount := (le_max_right ..).trans matchedRoom
    unfold ProfileTable.envelope at env
    omega
  have cap2 : 0<2*d.cap:=Nat.mul_pos (by decide) cap
  have pairs : 0<(s).pairs := by
    dsimp only [matcher,shape,Shape.pairs,entryCount,binCount]
    positivity
  have digit : 0<(s).digit := by
    change 0< max b (Nat.clog 2 (2+_+_+_+_))
    exact (Nat.clog_pos (by decide : 1<2) (by omega)).trans_le (le_max_right ..)
  have «prefix» : b≤(s).digit := le_max_left ..
  have uPos : 0<d.amount := (Nat.mul_pos digit pairs).trans_le matchWord
  obtain ⟨mPos,fill⟩:=occupancy payload d.amount uPos wide
  change 0< m at mPos
  have lo : (s).digit*B≤payload/2 := calc
    _ = (m)*((s).digit*(s).pairs) := by ring
    _ ≤ (m)*d.amount := Nat.mul_le_mul_left _ matchWord
    _ ≤ _ := lanes_fit payload d.amount
  have newShort : B≤payload := ((Nat.le_mul_of_pos_left _ digit).trans lo).trans (Nat.div_le_self ..)
  have newBits : b*B≤payload/2 := (Nat.mul_le_mul_right _ «prefix»).trans lo
  have larger : (m)≤B := Nat.le_mul_of_pos_right _ pairs
  have ratio : payload≤4*B*d.amount :=
    fill.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 larger))
  have padding : (dst).size≤2*(seats/B+2) :=
    Overlap.rounded (seats/B+1)
  exact DescentPackedProfileRepack.header_invoice base seats B d.colors (s).digit w payload d.hosts d.amount
    factor src dst large oldFit (Nat.mul_pos mPos pairs) newShort newBits ratio pages padding word

end
end Hierarchy.DescentSixParty.Chronology.DonorDate

end OAI
