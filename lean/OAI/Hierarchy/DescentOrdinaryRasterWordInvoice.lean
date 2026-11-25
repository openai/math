import OAI.Hierarchy.DescentRasterPlaneWordTariff
import OAI.Hierarchy.DescentOrdinaryRasterPrice

namespace OAI
/-! # Padded old-to-new return of the paid and actor quantities -/
namespace Hierarchy.DescentOrdinaryRasterReturn
open DescentVenueQuantityPlanes
variable (d : Dims)
local notation "N" => d.oldHosts*d.shapes
local notation "B" => d.blocks
local notation "H" => d.hosts
local notation "G" => d.groups
local notation "A" => d.oldLanes
local notation "M" => d.lanes

def fieldUnits (w₀ w₁ h : ℕ) :=(1+3*N+H)*h+N*(G*B)*w₀+(N+H)*G*w₁

theorem fee_word (w h oldUnit newUnit ratio : ℕ) (live : 0<M) (block : 0<B)
    (old : A≤h) (next : M*B≤h) (paidBits : 0<d.precision)
    (narrow : d.precision*A≤h/2) (reshaped : (d.precision*B)*M≤h/2)
    (fill₀ : h≤A*oldUnit) (fill₁ : h≤M*newUnit) (bus : w≤ratio*h) :
    fee d*w≤(ratio*(109+115*H))*h+
      2*(ratio*planeFactor d)*fieldUnits d oldUnit newUnit h+
      2*(ratio*(115*B+2048))*(2*(h+1)^2*2^(h/2))*h := by
  have oldOne : 1*A≤h/2:=(Nat.mul_le_mul_right _ paidBits).trans narrow
  have newOne : (1*B)*M≤h/2:=(Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ paidBits)).trans reshaped
  have paid:=DescentVenueQuantityPlanes.fee_word d w h oldUnit newUnit ratio live block old next narrow reshaped fill₀ fill₁ bus
  have alive:=DescentVenueQuantityPlanes.fee_word (actor d) w h oldUnit newUnit ratio live block old next oldOne newOne fill₀ fill₁ bus
  have roster : (4+10*H+7*(15*(H+1)))*w≤ratio*(109+115*H)*h :=by
    calc
      _ ≤ (4+10*H+7*(15*(H+1)))*(ratio*h) :=Nat.mul_le_mul_left _ bus
      _ = _ :=by ring
  unfold fee
  rw [Nat.add_mul,Nat.add_mul]
  exact (Nat.add_le_add (Nat.add_le_add roster paid) alive).trans_eq (by
    unfold actor DescentVenueQuantityPlanes.planeFactor fieldUnits
    dsimp only
    ring)

end Hierarchy.DescentOrdinaryRasterReturn

end OAI
