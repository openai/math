import OAI.Hierarchy.DescentPaidSweepWordVolume
import OAI.Hierarchy.DescentArgumentWidthArithmetic

namespace OAI
/-! # A fixed polynomial for the funded raster coefficients -/
namespace Hierarchy.DescentFundedRasterRowFeeRates
open DescentPaidResidentCount DescentArgumentWidthArithmetic

def rasterRate (opCost B D p u₀ u₁ u₂ : ℕ) :=
  WordVolume.rowRate B D p 7*(1+u₀+u₁)+224+
  2*(8192*(opCost+1)*(B+1))*(2+3*p+p*B*u₁+p*u₂+u₂)+
  (WordVolume.tableRate B D p 7+4*(115*B+2048))

theorem rasterRate_le {opCost B D p u₀ u₁ u₂ U : ℕ} (large : 8192≤U) (opRoom : opCost+1≤8192) (blocks : B≤U)
    (paths : D≤U^5) (shapes : p≤U) (old : u₀≤U^2) (work : u₁≤U^2) (new_ : u₂≤U^3) :
    rasterRate opCost B D p u₀ u₁ u₂≤U^24 :=by
  have pos : 0<U:=by omega
  have two : 2≤U:=by omega
  have num {c : ℕ} (hc : c≤8192) : c≤U^1:=one (hc.trans large)
  have b:=one blocks
  have s:=one shapes
  have row := add two
    (add two (mul (mul (num (by decide : 2≤8192)) b) (num (by decide : 7≤8192)))
      (mul (num (by decide : 2052≤8192)) b))
    (add two (add two (add two (mul (num (by decide : 2066≤8192)) b)
      (mul (num (by decide : 112≤8192)) paths)) (mul (num (by decide : 120≤8192)) s))
      (num (by decide : 6≤8192)))
  have fixed := add two (add two (add two (add two (mul (mul (num (by decide : 28≤8192)) b)
    (num (by decide : 7≤8192))) (mul (num (by decide : 358≤8192)) b))
    (mul (num (by decide : 1568≤8192)) paths)) (mul (num (by decide : 1730≤8192)) s))
    (num (by decide : 3029≤8192))
  have table := add two (add two (add two (add two fixed (num (by decide : 4096≤8192)))
    (mul (num (by decide : 230≤8192)) paths)) (mul (num (by decide : 460≤8192)) s))
    (num (by decide : 230≤8192))
  have plane := mul (mul (num (by decide : 8192≤8192)) (num opRoom))
    (add two b (num (by decide : 1≤8192)))
  have units := add two (add two (add two (add two (num (by decide : 2≤8192))
    (mul (num (by decide : 3≤8192)) s)) (mul (mul s b) work)) (mul s new_)) new_
  have volume := mul row (add two (add two (num (by decide : 1≤8192)) old) work)
  have correction := mul (num (by decide : 4≤8192))
    (add two (mul (num (by decide : 115≤8192)) b) (num (by decide : 2048≤8192)))
  exact raise pos (add two (add two (add two volume (num (by decide : 224≤8192)))
    (mul (mul (num (by decide : 2≤8192)) plane) units)) (add two table correction)) (by decide)

/-- Distribute the two field scans over their old and new row populations. The
three pitches multiply the occupied host/group rectangles; the lookup reserve
is counted once independently of the number of hosts. -/
theorem row_charge {opCost B D p H G R K h u₀ u₁ u₂ ratio Z : ℕ}
    (base : h≤Z) (oldH : H*h≤Z) (oldR : H*G≤Z) (newH : R*h≤Z) (newR : R*K≤Z)
    (crossR : H*K≤Z) (table : (h+1)^2*2^(h/2)*h≤Z) :
    ratio*WordVolume.rowRate B D p 7*(H*h+H*G*(u₀+u₁))+
      (ratio*(109+115*R))*h+
      2*(ratio*(8192*(opCost+1)*(B+1)))*
        ((1+3*(H*p)+R)*h+(H*p)*(K*B)*u₁+(H*p+R)*K*u₂)+
      (ratio*WordVolume.tableRate B D p 7+4*(ratio*(115*B+2048)))*
        ((h+1)^2*2^(h/2)*h) ≤ ratio*rasterRate opCost B D p u₀ u₁ u₂*Z :=by
  have source : H*h+H*G*(u₀+u₁)≤(1+u₀+u₁)*Z:=by
    calc _≤Z+Z*(u₀+u₁):=Nat.add_le_add oldH (Nat.mul_le_mul_right _ oldR)
         _=_:=by ring
  have fields : (1+3*(H*p)+R)*h+(H*p)*(K*B)*u₁+(H*p+R)*K*u₂≤(2+3*p+p*B*u₁+p*u₂+u₂)*Z:=by
    calc
      _ = h+3*p*(H*h)+R*h+(p*B*u₁)*(H*K)+(p*u₂)*(H*K)+u₂*(R*K):=by ring
      _ ≤ Z+3*p*Z+Z+(p*B*u₁)*Z+(p*u₂)*Z+u₂*Z:=by gcongr
      _ = _:=by ring
  have roster : (ratio*(109+115*R))*h≤ratio*224*Z:=by
    calc _ = ratio*(109*h+115*(R*h)):=by ring
         _ ≤ ratio*(109*Z+115*Z):=by gcongr
         _ = _:=by ring
  have charge:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.mul_le_mul_left (ratio*WordVolume.rowRate B D p 7) source) roster)
    (Nat.mul_le_mul_left (2*(ratio*(8192*(opCost+1)*(B+1)))) fields))
    (Nat.mul_le_mul_left (ratio*WordVolume.tableRate B D p 7+4*(ratio*(115*B+2048))) table)
  exact charge.trans_eq (by unfold rasterRate;ring)

end Hierarchy.DescentFundedRasterRowFeeRates

end OAI
