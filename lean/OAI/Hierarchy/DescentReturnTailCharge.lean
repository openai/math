import OAI.Hierarchy.DescentReturnTailNumbers
import OAI.Hierarchy.DescentFundedReturnVenue

namespace OAI
/-! # Word charge of the successor, metadata, operand output, and final pair-count clock -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook.MaterialProgram DescentPacking.PackedMatch.Local.Stage.DateBill
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
local notation "c" => v.nodeChart
local notation "s" => v.resolver
local notation "a" => v.area
local notation "d" => v.venue
local notation "h" => v.payload

theorem tail_paid (floor w ratio u A G g r : ℕ) (B : StageVenueTail.Sources) (room : v.ResultRoom floor B w)
    (live : 0<A) (bus : w≤ratio*h) (venue : (d).SourceRows h u) (shelves : v.ShelfRows u 1)
    (unit : 0<v.unit) (wide : 2*v.unit≤h) (count : v.countBits≤h/2)
    (hosts : (d).hosts≤A*g ∧ (s).hosts≤A*g ∧ (a).H≤A*2)
    (groups : (d).groups≤G ∧ (s).groups≤G ∧ (a).G≤G)
    (radix : 2^(d).k≤r ∧ (s).blocks≤r ∧ 2^(a).k≤r) (old : (a).unit≤u) :
    v.tailAmount floor w B room≤ratio*tailFactor g u r (d).degree (d).cap (s).nodes (s).operands*purchased A G h :=by
  let P₀:=purchased A G h
  let sh:=400000*(1+(r+(s).nodes+(s).operands+7))^4
  have native:=v.return_words floor w ratio u 1 B room bus venue shelves unit wide count
  have actor:=rectangle_paid («h»:=h) live hosts.1 groups.1 u
  have book:=return_volume_paid («h»:=h) live hosts.2.1 groups.2.1 u
  have prev:=return_volume_paid («h»:=h) live hosts.2.2 groups.2.2 (a).unit
  have page : (2*(h+1)^2*2^(h/2))*h≤P₀:=Nat.le_add_left ..
  have coeff : (c).ordinaryFactor 1 (s).operands 7+(v.finalChart.tickUnits 1+7*v.finalChart.textUnits)≤ sh:=by
    have «meta»:=(c).ordinaryFactor_le 1 (s).operands 7
    have final:=v.finalChart.finalFactor_le 1
    change (c).ordinaryFactor 1 (s).operands 7≤100000*(1+1)*(1+((s).blocks+(s).nodes+(s).operands+7))^4 at «meta»
    change _≤100000*(1+1)*(1+((s).blocks+(s).nodes+(s).operands))^4 at final
    apply (Nat.add_le_add «meta» final).trans
    have l₁ : 1+((s).blocks+(s).nodes+(s).operands+7)≤1+(r+(s).nodes+(s).operands+7):=by have:=radix.2.1;omega
    have l₂ : 1+((s).blocks+(s).nodes+(s).operands)≤1+(r+(s).nodes+(s).operands+7):=by have:=radix.2.1;omega
    dsimp only [sh]
    nlinarith only [Nat.pow_le_pow_left l₁ 4,Nat.pow_le_pow_left l₂ 4]
  have p₀ : volumeFactor 2 (a).unit≤volumeFactor 2 u:=by unfold volumeFactor;gcongr
  have pr : volumeBits (a).H (a).G h (a).unit≤volumeFactor 2 u*P₀:=prev.trans (Nat.mul_le_mul_right _ p₀)
  have r₀ : 2^((a).k+1)≤2*r:=by rw [pow_succ,Nat.mul_comm];exact Nat.mul_le_mul_left _ radix.2.2
  let vc:=4096*ratio*(r*(2*(d).cap)+1+2*(r+1))+1024*ratio*(r+(d).degree+1)
  let pc:=3*(2048*ratio)+115*ratio*r
  have vc' : ((d).wordCoefficients ratio).1≤vc:=by dsimp [StageVenueTail.Date.wordCoefficients,vc];gcongr <;> exact radix.1
  have pc' : ((d).wordCoefficients ratio).2≤pc:=by dsimp [StageVenueTail.Date.wordCoefficients,pc];gcongr; exact radix.1
  have pageBill : ((d).wordCoefficients ratio).2*(2*(h+1)^2*2^(h/2))*h ≤ pc*P₀ := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul pc' page
  apply native.trans
  calc
    _ ≤ (vc*(rectangleFactor g u*P₀)+pc*P₀)+2*ratio*sh*(volumeFactor g u*P₀)+
        2*ratio*(2000*(1+2*r))*(volumeFactor 2 u*P₀) := by
      apply Nat.add_le_add
      · exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul vc' actor) pageBill)
          (Nat.mul_le_mul (Nat.mul_le_mul_left _ coeff) book)
      · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add_left r₀ _))) pr
    _ = _ :=by unfold tailFactor;dsimp only [vc,pc,sh,P₀];ring

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
