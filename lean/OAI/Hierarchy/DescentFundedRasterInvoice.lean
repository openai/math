import OAI.Hierarchy.DescentDatedOrdinaryFundedRaster
import OAI.Hierarchy.DescentPaidSweepHeldTariff
import OAI.Hierarchy.DescentOrdinaryRasterPrice
import OAI.Hierarchy.DescentOrdinaryWordTariff

namespace OAI
/-! # Ordinary funded and actor raster publication at the actual successor addresses -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentPaidResidentCount DescentPackedColony DescentPacking.PackedMatch.Local.Stage
open DescentSharedCableNames DescentOrdinaryRasterReturn DescentVenueQuantityPlanes
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ)
local notation "a" => v.area
local notation "start" => v.endAddress floor
local notation "H" => (a).H
local notation "G" => (a).G
local notation "old" => (a).lanesAt
local notation "M" => v.rasterLanes
local notation "p" => StageVenueTail.OrdinaryRaster.shapes a
local notation "paths" => StageVenueTail.OrdinaryRaster.paths a
local notation "n" => StageVenueTail.OrdinaryRaster.nameBits a
local notation "b" => v.venue.paidBits
local notation "cap" => (a).cap
local notation "k" => (a).k
local notation "dims" => StageVenueTail.OrdinaryRaster.dims a v.venue M
local notation "labels" => (fun l : Fin p=>Packed.token (some l))
local notation "top" => StageVenueTail.OrdinaryRaster.sweep a v.venue M start
local notation "begin_" => StageVenueTail.OrdinaryRaster.prepared a v.venue M start

variable (B : v.FundedInputs) (i : Dated.Operands) (w : ℕ) (safe : v.FundedRoom floor B i w)
local notation "banks" => v.paidRasterBanks floor
local notation "gather_" => Sweep.HeldRepacked.program start H G old M k paths cap b n p B.field B.ports i.atoms labels
local notation "cost_" => Sweep.HeldRepacked.ticks start H G old M k paths cap b n p B.field B.ports i.atoms labels
local notation "scatter" => DescentOrdinaryRasterReturn.phase dims banks top w

def fundedInvoice (unit : ℕ) : ℕ :=
  Sweep.HeldRepacked.bill start H G old M k paths cap b n p unit+DescentOrdinaryRasterReturn.fee dims

theorem funded_word_bill (unit : ℕ) (work : ∀j<2^k,(i.atoms j).work≤unit)
    (positive : 0<old) (clipped : 0<M) (next : 0<v.venue.paidLanes) :
    DateBill.bitTariff (v.fundedRaster floor B i w safe).program (v.fundedRaster floor B i w safe).ticks ≤
      v.fundedInvoice floor unit*w := by
  have earlier:=Sweep.HeldRepacked.tariff start H G old M k paths cap b n p B.field B.ports i.atoms labels w unit work positive clipped
  have later:=DescentOrdinaryRasterReturn.billed dims banks top w clipped next (Nat.two_pow_pos _)
  change ((cost_ w+(scatter).ticks)+7*DescentStaticWordColumn.names ((gather_ w).seq (scatter).program))*w≤_
  rw [DescentStaticWordColumn.names_seq]
  apply Nat.mul_le_mul_right
  unfold fundedInvoice
  omega

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
