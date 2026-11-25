import OAI.Computability.BorderVNP.CellTeamSignedScales
import OAI.Computability.BorderVNP.CellSparseExteriorTeamCost

/-! # The rounded team clock for the physical sparse argument path -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open TeamScales VPVNP CellPacketGeometry

/-- Sum the actual prepared-call, sparse exterior and occurrence allowances.
Each coefficient is independent of the stretched batch length and the team. -/
theorem sparse_cell_charge {p d w X R H B global localCount units prefixSize prepared compression reports : ℕ}
    (fit : global ≤ 2^p) (localFit : localCount ≤ global)
    (encoded : prefixSize ≤ 6*(w+1)*(2*(1000000*X/256)+X+global))
    (mass : units ≤ 2*(w+1)*(2^p+2^d)+18*(w+1)*X+2*X+prefixSize+R*(H*B))
    (typed : prepared ≤ 64+11*global+100*localCount+308*units)
    (sparse : compression ≤ 40+200*(w+1)*(global+(2*(1000000*X/256)+X))+7*(2^p+R*(H*B)))
    (occurrence : reports ≤ 54+79*localCount+105*2^p+516*X+131*(R*(H*B))) :
    prepared+compression+reports ≤ 5000*((w+1)*(2^p+2^d))+700000000*((w+1)*X)+500*(R*(H*B)) := by
  let G := (w+1)*(2^p+2^d)
  let L := (w+1)*X
  have pub : 2^p ≤ G := (Nat.le_add_right ..).trans (Nat.le_mul_of_pos_left _ (by omega))
  have one : 1 ≤ 2^p := Nat.one_le_two_pow
  have live : X ≤ L := Nat.le_mul_of_pos_left _ (by omega)
  have geo : (w+1)*global ≤ G := Nat.mul_le_mul_left _ (fit.trans (Nat.le_add_right ..))
  have div : 1000000*X/256 ≤ 4000*X := by omega
  have volume : (w+1)*(2*(1000000*X/256)+X) ≤ 8001*L :=
    (Nat.mul_le_mul_left (w+1) (show 2*(1000000*X/256)+X ≤ 8001*X by omega)).trans_eq (by dsimp only [L]; ring)
  rw [Nat.mul_assoc,Nat.mul_add] at encoded
  rw [Nat.mul_assoc 200,Nat.mul_add (w+1),Nat.mul_add 7] at sparse
  rw [Nat.mul_assoc 2,Nat.mul_assoc 18] at mass
  change units ≤ 2*G+18*L+2*X+prefixSize+R*(H*B) at mass
  change prepared+compression+reports ≤ 5000*G+700000000*L+500*(R*(H*B))
  omega

/-- Apply the real geometry and word-size allowances to the actual RLE schedule. -/
theorem sparse_cell_scale (p d k u b w a D n r R : ℕ) (α ξ A L : ℝ)
    (hL : 0 ≤ L) (hn : 1 ≤ n) (hr : 1 ≤ r) (hξ : ξ ≤ 1) (hD : 1 ≤ D) (bw : 1 ≤ b) (ww : 1 ≤ w)
    (geo : (GeometryAdviceRate.ticks k u (Total p d) b w : ℝ) ≤ A*publicWork a α r n R)
    (words : (w:ℝ)+1 ≤ L*(logWidth r n:ℝ)^D)
    (positions : ℕ) (origin : positions ≤ r*logWidth r n) (cost : ℕ)
    (physical : cost ≤ 5000*((w+1)*(2^p+2^d)) + 700000000*((w+1)*exterior ξ r n) + 500*positions) :
    (cost : ℝ) ≤ 5000*A*publicWork a α r n R+(700000000*L+500)*localWork a D α ξ r n R := by
  simpa using cell_scale 5000 700000000 500 p d k u b w a D n r R α ξ A L hL hn hr hξ hD bw ww
    geo words positions origin cost physical

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
