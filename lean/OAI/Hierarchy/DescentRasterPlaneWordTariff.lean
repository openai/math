import OAI.Hierarchy.DescentVenueQuantityPrice
import OAI.Hierarchy.DescentOrdinaryOverlapReserve
import OAI.Hierarchy.DescentPackedRegroup
import OAI.Hierarchy.DescentPackedChunkWork
import OAI.Hierarchy.DescentRasterPlaneRows
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Cost of the compact old-to-new funded census and actor quantities -/
namespace Hierarchy.DescentVenueQuantityPlanes
open DescentSIMDLookup DescentActorRaster DescentDyadicSpan
noncomputable section
variable (d : Dims)
local notation "B" => d.blocks
local notation "R" => d.hosts
local notation "N" => d.oldHosts*d.shapes
local notation "G" => d.groups
local notation "A" => d.oldLanes
local notation "M" => d.lanes
local notation "s" => chunks G M
local notation "b" => d.precision
local notation "pages" => (Overlap.pieces (G*B) A (M*B)+1)*(A+1)*2^(b*A)

private theorem dense_cells (blocks hosts lanes raw : ℕ) :
    DenseRead.cells blocks hosts lanes 0 raw ≤ 4*(blocks*(hosts*lanes))+2*raw+3 := by
  change 2*span (blocks*(hosts*lanes))+span raw≤_
  have hs:=span_le (blocks*(hosts*lanes))
  have hr:=span_le raw
  omega

def planeFactor (d : Dims) := 8192*(denseOp+1)*(d.blocks+1)

theorem fee_rows (live : 0<M) (block : 0<B) :
    fee d≤ planeFactor d*(1+N+N*chunks (G*B) A+N*s+R*s)+
       (115*B)*2^((b*B)*M)+2048*pages := by
  have cells:=dense_cells B R s N
  have group:=chunks_group G M B live block
  have charged:=charge_rows B denseOp (N*chunks (G*B) A) (N*s) (R*s) N
    (DenseRead.cells B R s 0 N) pages (2^((b*B)*M)) (by simpa only [Nat.mul_assoc] using cells)
  refine Eq.trans_le ?_ charged
  unfold fee tableScanBill DescentScalarBookReshape.cells Overlap.rows rowCharge
  rw [group,show d.shapes*d.oldHosts=N by ring]
  ring

/-- Incoming and outgoing occupancy may come from different clipped pitches.
The two independent lookup tables are charged once for the whole phase. -/
theorem fee_word (w h oldUnit newUnit ratio : ℕ) (live : 0<M) (block : 0<B)
    (old : A≤h) (next : M*B≤h) (narrow : b*A≤h/2) (reshaped : (b*B)*M≤h/2)
    (occup₀ : h≤A*oldUnit) (occup₁ : h≤M*newUnit) (bus : w≤ratio*h) :
    fee d*w ≤ ratio*planeFactor d*((1+3*N+R)*h+N*(G*B)*oldUnit+(N+R)*G*newUnit)+
      ratio*(115*B+2048)*(2*(h+1)^2*2^(h/2))*h := by
  let lookup:=2*(h+1)^2*2^(h/2)
  have power : 2^((b*B)*M)≤lookup := by
    calc
      _ ≤ 2^(h/2):=Nat.pow_le_pow_right (by decide) reshaped
      _ ≤ lookup :=by
        change 2^(h/2)≤2*(h+1)^2*2^(h/2)
        exact Nat.le_mul_of_pos_left _ (by positivity)
  have tables : pages≤lookup :=Overlap.half_pages h (G*B) A (M*B) b old next narrow
  have src:=DescentDatedSeedStartup.chunk_work N (G*B) A h oldUnit occup₀
  have dst:=DescentDatedSeedStartup.chunk_work N G M h newUnit occup₁
  have recv:=DescentDatedSeedStartup.chunk_work R G M h newUnit occup₁
  have rows : (1+N+N*chunks (G*B) A+N*s+R*s)*h ≤
      (1+3*N+R)*h+N*(G*B)*oldUnit+(N+R)*G*newUnit := by
    calc
      _ = h+N*h+(N*chunks (G*B) A)*h+(N*s)*h+(R*s)*h :=by ring
      _ ≤ h+N*h+(N*h+N*(G*B)*oldUnit)+(N*h+N*G*newUnit)+(R*h+R*G*newUnit) :=by gcongr
      _ = _ :=by ring
  calc
    _ ≤ (planeFactor d*(1+N+N*chunks (G*B) A+N*s+R*s)+(115*B)*2^((b*B)*M)+2048*pages)*(ratio*h) :=
      Nat.mul_le_mul (fee_rows d live block) bus
    _ = ratio*planeFactor d*((1+N+N*chunks (G*B) A+N*s+R*s)*h)+
        ratio*((115*B)*2^((b*B)*M)+2048*pages)*h :=by ring
    _ ≤ ratio*planeFactor d*((1+3*N+R)*h+N*(G*B)*oldUnit+(N+R)*G*newUnit)+
        ratio*((115*B)*lookup+2048*lookup)*h :=by gcongr
    _ = _ :=by unfold lookup;ring

end
end Hierarchy.DescentVenueQuantityPlanes

end OAI
