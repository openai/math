import OAI.Hierarchy.DescentFundedRasterRowFeeRates
import OAI.Hierarchy.DescentFundedRasterScaled
import OAI.Hierarchy.DescentArgumentRowVolume
import OAI.Hierarchy.DescentRegisteredSelectorScale

namespace OAI
/-! # Row-volume price of the funded paid and actor rasters -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPackedColony DescentPacking.PackedMatch.Local.Stage DescentPaidResidentCount
open DescentArgumentWidthArithmetic DescentVenueQuantityPlanes DescentOrdinaryRasterReturn DescentFundedRasterRowFeeRates
noncomputable section

variable {F P : Type} [Field F] {v : PhysicalOrdinary F P} {A : ArgumentEntry v} {S : DescentCompiler.AtomSchedule} {i : ℕ}

/-- The two native field scans share the attained host and group populations.
Only their shape multiplicity and their actual old and new pitches enter the local rate. -/
theorem SectionPopulation.funded_fee_rows (pop : SectionPopulation v A S i) (h u₀ u₁ u₂ ratio U : ℕ)
    (radix : v.vector.radix=S.radix) (positive : 0<v.vector.radix) (large : 8192≤U)
    (blocks : 2^v.area.k≤U) (paths : (v.area.D+1)^4*2^v.area.k≤U^5)
    (shapes : StageVenueTail.OrdinaryRaster.shapes v.area≤U)
    (old : u₀≤U^2) (work : u₁≤U^2) (new_ : u₂≤U^3) :
    v.fundedFee h u₀ u₁ u₂ 7 ratio≤ratio*U^24*v.rowVolume h :=by
  let Z:=v.rowVolume h
  let a:=v.area
  let B:=2^a.k
  let p:=StageVenueTail.OrdinaryRaster.shapes a
  let D:=(a.D+1)^4*B
  let d:=StageVenueTail.OrdinaryRaster.dims a v.venue v.rasterLanes
  have bounds:=pop.native_rows h radix positive
  obtain ⟨base,h₀,h₁,r₀,r₁,_,_,_,_,_,table,_⟩:=bounds
  have oldH : a.H*h≤Z:=h₀
  have oldR : a.H*a.G≤Z:=r₀
  have newH : v.venue.hosts*h≤Z:=by rw [pop.venue.1];exact h₁
  have newR : v.venue.hosts*v.venue.groups≤Z:=by rw [pop.venue.1,pop.venue.2];exact r₁
  have smallG : v.venue.groups≤a.G:=by
    change v.venue.groups≤v.material.oldGroups
    rw [pop.venue.2,pop.material.2,pop.donor.2,←pop.group_partition]
    exact Nat.le_mul_of_pos_right _ (radix ▸ positive)
  have crossR : a.H*v.venue.groups≤Z:=(Nat.mul_le_mul_left _ smallG).trans oldR
  calc
    _ ≤ ratio*rasterRate denseOp B D p u₀ u₁ u₂*Z:=
      row_charge base oldH oldR newH newR crossR table
    _ ≤ _:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (rasterRate_le large (by decide : denseOp+1≤8192) blocks paths shapes old work new_))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

namespace Hierarchy.DescentSixParty.Chronology.OrdinaryBooks
open Computability.BorderVNP.Crossing DescentDatedAddressBook DescentPacking.PackedMatch.Local
open DescentArgumentWidthArithmetic ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {d k age z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {src : Reached W G q ε S k age z D wire hist} {he : 0≤ ε} {T : StageInput W G u ε}
    {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
    {dst : Reached n.result G q ε S k (age+1) z' D' wire hist}
    (ticket : OrdinaryLink src he T c n dst)
    (gain tail p f payload seats hostLanes : ℕ) (old : Bank) (ordinary : ℕ→Stage.Dated.Ordinary)
    (op : RotorSpec) (drift degree : ℕ) (prior : DatePorts) (floor : ℕ)
local notation "Lₑ" => atDate G S op gain k age p tail drift degree payload seats prior
local notation "baseₑ" => (Lₑ).onTicket ticket gain tail p f payload seats hostLanes old ordinary
local notation "extₑ" => (baseₑ).argumentUnitFrom prior floor
local notation "Yₑ" => (baseₑ).registeredFrom prior floor

/-- Specialize to the clip and the three units selected by the issued argument
pages. The dated reference degree identifies the native roster's precise length. -/
theorem registered_funded_raster_rows (U ratio : ℕ) (large : 8192≤U)
    (sizes : ∀j,(Lₑ).bookMouthParameters j≤U)
    (actual : src.placement.degree=(Lₑ).reference.degree)
    (funds : (baseₑ).fundedMaxUnit extₑ≤U)
    (site : PhysicalOrdinary.SectionPopulation Yₑ ((baseₑ).registeredEntry prior floor) S age)
    (radix : S.radix=2^k) :
    (Yₑ).fundedFee payload (4*(baseₑ).area.unit) ((baseₑ).fundedWorkingUnit extₑ)
      (2^k*(baseₑ).fundedWorkingUnit extₑ) 7 ratio≤ratio*U^24*(Yₑ).rowVolume payload :=by
  let v:=baseₑ
  let e:=extₑ
  let Y:=Yₑ
  have pos : 0<U:=by omega
  have B : 2^k≤U:=sizes 2
  have degreeB : Y.area.D+1≤U:=by
    change src.placement.degree+1≤U
    rw [actual]
    exact sizes 1
  have shapeB : StageVenueTail.OrdinaryRaster.shapes Y.area≤U:=by
    change (2^(k+1)-1)*DescentOrdinaryVenueReturn.shapeSlots src.placement.degree≤U
    rw [actual]
    exact sizes 6
  have paid : v.area.unit≤U := ((v.source_density e).1).trans funds
  have obtainWork : v.fundedWorkingUnit e≤U^2:=by
    rw [v.funded_density_exact]
    exact mul (one (show 8≤U by omega)) (one funds)
  exact site.funded_fee_rows payload _ _ _ ratio U radix.symm (Nat.two_pow_pos k) large
    B (mul (Nat.pow_le_pow_left degreeB 4) (one B)) shapeB
    (mul (one (show 4≤U by omega)) (one paid)) obtainWork (mul (one B) obtainWork)

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryBooks

end OAI
