import OAI.Hierarchy.DescentOrdinaryVenuePrice
import OAI.Hierarchy.DescentOrdinaryWordTariff

namespace OAI
/-! # The compact public peer, successor host and hub tables cost only common-host words -/
namespace Hierarchy.DescentOrdinaryVenueReturn
open DescentDyadicSpan DescentSixParty.Chronology DescentPacking.PackedMatch.Local.Stage.DateBill

/-- The old array has at most two padded rows per purchased host. The successor
array has at most `growth` rows per purchased host. -/
def hostFee (degree growth nextDegree : ℕ) :=
  7*(15000*3*(degree+12)^50+300*(growth*nextDegree)+100+800)+
  (4+10*(2*(2*growth+1)))+7*(15*(2*(2*growth+1)+1))+
  (4+growth*(2*hubOp+4))+7*(11+4*hubOp)

theorem fee_hosts (H D R E purchased degree growth nextDegree : ℕ) (live : 0<purchased)
    (old : H≤2*purchased) (fresh : R≤purchased*growth) (degreeFit : D≤degree) (nextFit : E≤nextDegree) :
    fee H D R E≤purchased*hostFee degree growth nextDegree := by
  have up (n : ℕ) : n≤purchased*n:=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right n live
  have padded : span R≤purchased*(2*growth+1):=calc
    _ ≤ 2*R+1:=span_le R
    _ ≤ 2*(purchased*growth)+purchased:=Nat.add_le_add (Nat.mul_le_mul_left _ fresh) live
    _ = _ :=by ring
  have oldPad : H+1≤purchased*3 :=by omega
  have power:=(Nat.pow_le_pow_left (Nat.add_le_add_right degreeFit 12) 50)
  have oldCharge := Nat.mul_le_mul (Nat.mul_le_mul_left 15000 oldPad) power
  have newCharge := Nat.mul_le_mul fresh nextFit
  have hubCharge := Nat.mul_le_mul_right (2*hubOp+4) fresh
  have fixedCharge := up (11+4*hubOp)
  unfold fee hostFee
  calc
    _ ≤ 7*(15000*(purchased*3)*(degree+12)^50+300*((purchased*growth)*nextDegree)+50*(2*purchased)+purchased*800)+
      (purchased*4+10*(2*(purchased*(2*growth+1))))+
      7*(15*(2*(purchased*(2*growth+1))+purchased))+
      (purchased*4+(purchased*growth)*(2*hubOp+4))+7*(purchased*(11+4*hubOp)) := by
        omega
    _ = _ := by
      generalize (degree+12)^50 = poly
      ring

theorem billed_on_hosts (B : Sources) (base k H D R E w payload ratio purchased degree growth nextDegree : ℕ)
    (bus : w≤ratio*payload) (live : 0<purchased) (old : H≤2*purchased) (fresh : R≤purchased*growth)
    (degreeFit : D≤degree) (nextFit : E≤nextDegree) :
    let p:=phase B base k H D R E w
    bitTariff p.program p.ticks≤purchased*payload*(ratio*hostFee degree growth nextDegree) := by
  intro p
  have actual:=(billed B base k H D R E w).trans (fee_hosts H D R E purchased degree growth nextDegree
    live old fresh degreeFit nextFit)
  exact (Nat.mul_le_mul actual bus).trans_eq (by ring)

end Hierarchy.DescentOrdinaryVenueReturn

end OAI
