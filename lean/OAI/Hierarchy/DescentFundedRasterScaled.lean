import OAI.Hierarchy.DescentFundedRasterInvoice
import OAI.Hierarchy.DescentPaidSweepScaled
import OAI.Hierarchy.DescentOrdinaryRasterWordInvoice

namespace OAI
/-! # Word charge for the chosen clip and the successor's paid and actor wiring -/
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


local notation "D₀" => paths*2^k
local notation "G₁" => v.venue.groups
local notation "M₁" => v.venue.paidLanes

/-- Actual three pitches used by the incoming matcher, the clipped raster and the next receiver. -/
structure FundedCaps (h w₀ w₁ w₂ : ℕ) : Prop where
  positive : 0<old
  clipped : 0<M
  out : 0<M₁
  oldCap : old≤h
  clipCap : M≤h
  outCap : M₁*2^k≤h
  paid : 0<b
  raw : b*old≤h/2
  table : (b*D₀+b)*M≤h/2
  masks : Sweep.maskBits D₀ cap n M≤h/2
  sums : Sweep.sumBits D₀ cap b M≤h/2
  clipBits : b*M≤h/2
  outBits : (b*2^k)*M₁≤h/2
  fill₀ : h≤old*w₀
  fill₁ : h≤M*w₁
  fill₂ : h≤M₁*w₂

/-- Native row and lookup charge of the packed funded raster at the three attained occupancies. -/
def fundedFee (h w₀ w₁ w₂ unit ratio : ℕ) : ℕ :=
      ratio*WordVolume.rowRate (2^k) D₀ p unit*(H*h+H*G*(w₀+w₁))+
      (ratio*(109+115*v.venue.hosts))*h+
      2*(ratio*(DescentVenueQuantityPlanes.planeFactor dims))*DescentOrdinaryRasterReturn.fieldUnits dims w₁ w₂ h+
      (ratio*WordVolume.tableRate (2^k) D₀ p unit+4*(ratio*(115*2^k+2048)))*
        ((h+1)^2*2^(h/2)*h)

theorem funded_scaled (h w₀ w₁ w₂ unit ratio : ℕ) (work : ∀j<2^k,(i.atoms j).work≤unit)
    (bus : w≤ratio*h) (positive : 0<old) (clipped : 0<M) (out : 0<M₁)
    (oldCap : old≤h) (clipCap : M≤h) (outCap : M₁*2^k≤h)
    (paid : 0<b) (raw : b*old≤h/2) (table : (b*D₀+b)*M≤h/2)
    (masks : Sweep.maskBits D₀ cap n M≤h/2) (sums : Sweep.sumBits D₀ cap b M≤h/2)
    (clipBits : b*M≤h/2) (outBits : (b*2^k)*M₁≤h/2)
    (fill₀ : h≤old*w₀) (fill₁ : h≤M*w₁) (fill₂ : h≤M₁*w₂) :
    DateBill.bitTariff (v.fundedRaster floor B i w safe).program (v.fundedRaster floor B i w safe).ticks ≤
      ratio*WordVolume.rowRate (2^k) D₀ p unit*(H*h+H*G*(w₀+w₁))+
      (ratio*(109+115*v.venue.hosts))*h+
      2*(ratio*(DescentVenueQuantityPlanes.planeFactor dims))*DescentOrdinaryRasterReturn.fieldUnits dims w₁ w₂ h+
      (ratio*WordVolume.tableRate (2^k) D₀ p unit+4*(ratio*(115*2^k+2048)))*
        ((h+1)^2*2^(h/2)*h) := by
  have source:=v.funded_word_bill floor B i w safe unit work positive clipped out
  have census:=Sweep.HeldRepacked.scaled start H G old M k paths cap b n p unit h w ratio w₀ w₁
    bus oldCap clipCap raw table masks sums fill₀ fill₁
  have planes:=DescentOrdinaryRasterReturn.fee_word dims w h w₁ w₂ ratio out (Nat.two_pow_pos _) clipCap outCap
    paid clipBits outBits fill₁ fill₂ bus
  unfold fundedInvoice at source
  rw [Nat.add_mul] at source
  exact (source.trans (Nat.add_le_add census planes)).trans_eq (by dsimp only [StageVenueTail.OrdinaryRaster.dims];ring)


theorem funded_caps_bill (h w₀ w₁ w₂ unit ratio : ℕ) (work : ∀j<2^k,(i.atoms j).work≤unit)
    (bus : w≤ratio*h) (caps : v.FundedCaps h w₀ w₁ w₂) :
    DateBill.bitTariff (v.fundedRaster floor B i w safe).program (v.fundedRaster floor B i w safe).ticks ≤
      v.fundedFee h w₀ w₁ w₂ unit ratio :=
  v.funded_scaled floor B i w safe h w₀ w₁ w₂ unit ratio work bus caps.positive caps.clipped caps.out
    caps.oldCap caps.clipCap caps.outCap caps.paid caps.raw caps.table caps.masks caps.sums
    caps.clipBits caps.outBits caps.fill₀ caps.fill₁ caps.fill₂

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
