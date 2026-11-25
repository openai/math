import OAI.Hierarchy.DescentResetControlRegisterRun
import OAI.Hierarchy.DescentResetQuantityFunded

namespace OAI
/-! The control quantities and the following native scalar activation dictionary
occupy the same compact host volume. -/
namespace Hierarchy.DescentResetControlRegisters.Chart
open DescentVenueQuantityPlanes DescentDatedAddressBook.CandidateFront DescentSIMDLookup
noncomputable section

theorem fee_funded (c : Chart) (h : ℕ) (blocks : 0<c.dims.blocks) (lanes : 0<c.dims.lanes)
    (oldPitch : c.dims.oldLanes≤h) (newPitch : c.dims.lanes≤h)
    (oldTable : c.dims.precision*c.dims.oldLanes≤h/2)
    (newTable : (c.dims.precision*c.dims.blocks)*c.dims.lanes≤h/2)
    (mask : (c.bits+1)*c.dims.lanes≤h/2) :
    c.fee≤(resetPlaneFactor c.dims.blocks+4096)*planeEnvelope c.dims h := by
  let p:=c.dims
  let A:=planeEnvelope p h
  let rows:=p.hosts*chunks p.groups p.lanes
  let raw:=p.oldHosts*p.shapes
  have one : 1≤A := Nat.le_add_right ..
  have data : rows≤A := by dsimp only [A,planeEnvelope,stemEnvelope,rows]; omega
  have old : raw≤A := by dsimp only [A,planeEnvelope,stemEnvelope,raw]; omega
  have shared : (h+1)^3*2^(h/2)≤A := by dsimp only [A,planeEnvelope,stemEnvelope]; omega
  have half : c.bits+p.lanes≤h/2 := by
    have t:=Nat.le_mul_of_pos_right c.bits lanes
    rw [Nat.add_mul,Nat.one_mul] at mask
    exact (Nat.add_le_add_right t p.lanes).trans mask
  have tab : 2^(c.bits+p.lanes)≤A :=
    (Nat.pow_le_pow_right (by decide) half).trans ((Nat.le_mul_of_pos_left _ (by positivity)).trans shared)
  have lit : 2^c.bits ≤ A :=
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right c.bits p.lanes)).trans tab
  have r:=padded_length rows
  have s:=padded_length raw
  have count : c.count≤11*A := by
    change 2^Nat.clog 2 rows+2^Nat.clog 2 raw+2^Nat.clog 2 raw+2^c.bits+2^(c.bits+p.lanes)≤11*A
    omega
  have charge:=DescentVenueQuantityPlanes.fee_funded c.dims h blocks lanes oldPitch newPitch oldTable newTable
  change DescentVenueQuantityPlanes.fee p+4+10*c.count+7*(15*(c.count+1))≤(resetPlaneFactor p.blocks+4096)*A
  rw [Nat.add_mul]
  change DescentVenueQuantityPlanes.fee p≤resetPlaneFactor p.blocks*A at charge
  omega

end
end Hierarchy.DescentResetControlRegisters.Chart

end OAI
