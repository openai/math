import OAI.Computability.BorderVNP.CellTeamOccurrenceClock
import OAI.Computability.BorderVNP.CellTeamSupplementalClock
import OAI.Computability.BorderVNP.RoutingISAEvalClock
import OAI.Computability.BorderVNP.ResidueAdviceBudget

/-! # Absorbing true cell preparation and original unary occurrences into the team clock -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open TeamScales VPVNP ParseTable CellPacketGeometry

/-- In the actual degree-`n` coefficient chart the number of batch/parameter pairs
fits the replication budget of the stretched sequence. -/
theorem chart_pairs_le (k s r R : ℕ) (teams : R ≤ k+1) (rep : (k+1+s+2)^24 ≤ r) :
    R*Branch.parameterCount (2*(k+1)) k s ≤ r := by
  let n := k+1
  let M := n+s+2
  have two : 2 ≤ M := by dsimp [M]; omega
  have small : n ≤ M := by dsimp [M]; omega
  have vars : 2*n+s+1 ≤ 2*M := by dsimp [M]; omega
  have par : Branch.parameterCount (2*n) k s ≤ (2*n+s+1)*(2*n) + n^2*(2*n+s+1)^3 := by
    simpa only [Branch.parameterCount,Fintype.card_fin] using parameter_count_le (Fin (2*n)) k s
  have deg : M^2 ≤ M^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have factor : 12 ≤ M^4 := (by decide : 12 ≤ 2^4).trans (Nat.pow_le_pow_left two 4)
  have coeff : Branch.parameterCount (2*n) k s ≤ 12*M^5 := calc
    _ ≤ (2*M)*(2*M)+M^2*(2*M)^3 := par.trans (by gcongr)
    _ ≤ _ := by nlinarith only [deg]
  calc
    R*Branch.parameterCount (2*(k+1)) k s ≤ M*(12*M^5) := Nat.mul_le_mul (teams.trans small) coeff
    _ ≤ M*(M^4*M^5) := Nat.mul_le_mul_left M (Nat.mul_le_mul_right _ factor)
    _ = M^10 := by ring
    _ ≤ M^24 := Nat.pow_le_pow_right (by omega) (by decide)
    _ ≤ r := rep

/-- The request-count bit width in Section 11 fits the true logarithmic address
scale. This includes the final `+1` inside the binary ceiling. -/
theorem request_bits_le {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) :
    Nat.clog 2 (r*(2*n-1)+1) ≤ logWidth r n := by
  have h : (2*n-1)+1=2*n := by omega
  have step : r*((2*n-1)+1)=r*(2*n-1)+r := by ring
  rw [h] at step
  have rep : logWidth r n = Nat.clog 2 (2*n*r) := by
    unfold logWidth
    rw [← Real.natCeil_logb_natCast]
    norm_cast
  rw [rep]
  apply Nat.clog_mono_right
  rw [Nat.mul_comm (2*n)]
  omega

/-- The global number of potential expanded power positions is paid by one
logarithmic factor times the true batch length. -/
theorem chart_power_le (k s r R : ℕ) (hr : 1 ≤ r) (teams : R ≤ k+1) (rep : (k+1+s+2)^24 ≤ r) :
    R*(Branch.parameterCount (2*(k+1)) k s*Nat.clog 2 (r*(2*(k+1)-1)+1)) ≤ r*logWidth r (k+1) := by
  rw [←Nat.mul_assoc]
  exact Nat.mul_le_mul (chart_pairs_le k s r R teams rep) (request_bits_le (by omega) hr)

/-- Summing the native prepared-call and report allowances from the physical
geometry, ownership, incoming bits and power-slot bounds. -/
theorem signed_cell_charge {p d w X R H B global localCount U prep reports : ℕ}
    (fit : global ≤ 2^p) (localFit : localCount ≤ global)
    (units : U ≤ 2*(w+1)*(2^p+2^d)+18*(w+1)*X+3*X+2*(1000000*X/256)+R*(H*B))
    (prepared : prep ≤ 64+11*global+100*localCount+308*U)
    (occurrence : reports ≤ 54+79*localCount+105*2^p+516*X+131*(R*(H*B))) :
    prep+reports ≤ 1200*((w+1)*(2^p+2^d)) + 700000000*((w+1)*X) + 439*(R*(H*B)) := by
  have big := Nat.div_le_self (1000000*X) 256
  have pub : 2^p ≤ (w+1)*(2^p+2^d) := (Nat.le_add_right ..).trans (Nat.le_mul_of_pos_left _ (by omega))
  have one := Nat.one_le_two_pow (n:=p)
  have live : X ≤ (w+1)*X := Nat.le_mul_of_pos_left _ (by omega)
  rw [Nat.mul_assoc 2] at units
  rw [Nat.mul_assoc 18] at units
  omega

/-- Charge fixed multiples of the public geometry work, the live exterior bits and
the original parameter positions to the true logarithmic team scale. -/
theorem cell_scale (publicFactor liveFactor useFactor : ℕ) (p d k u b w a D n r R : ℕ) (α ξ A L : ℝ)
    (hL : 0 ≤ L) (hn : 1 ≤ n) (hr : 1 ≤ r) (hξ : ξ ≤ 1) (hD : 1 ≤ D)
    (bw : 1 ≤ b) (ww : 1 ≤ w)
    (geo : (GeometryAdviceRate.ticks k u (Total p d) b w : ℝ) ≤ A*publicWork a α r n R)
    (words : (w:ℝ)+1 ≤ L*(logWidth r n:ℝ)^D)
    (positions : ℕ) (origin : positions ≤ r*logWidth r n) (cost : ℕ)
    (physical : cost ≤ publicFactor*((w+1)*(2^p+2^d)) + liveFactor*((w+1)*exterior ξ r n) + useFactor*positions) :
    (cost : ℝ) ≤ publicFactor*A*publicWork a α r n R+(liveFactor*L+useFactor)*localWork a D α ξ r n R := by
  let X : ℝ := exterior ξ r n
  let scale : ℝ := (logWidth r n:ℝ)^D
  have geot := TypedBatch.geometry_words_le_ticks p d k u b w bw ww
  have g : (((w+1)*(2^p+2^d):ℕ):ℝ) ≤ A*publicWork a α r n R :=
    (by exact_mod_cast geot : (((w+1)*(2^p+2^d):ℕ):ℝ) ≤ (GeometryAdviceRate.ticks k u (Total p d) b w:ℝ)).trans geo
  have xp : 0 ≤ X := by dsimp [X]; positivity
  have npos : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have oneWidth : 1 ≤ width n (1-ξ) :=
    Nat.le_floor (by simpa using Real.one_le_rpow npos (sub_nonneg.mpr hξ))
  have rx : (r:ℝ) ≤ X := by
    dsimp only [X]
    exact_mod_cast (Nat.le_mul_of_pos_right r oneWidth : r ≤ exterior ξ r n)
  have logs : 1 ≤ (logWidth r n:ℝ) := by exact_mod_cast (GeometryAdviceRate.indexWidths hr hn).1
  have pow : (logWidth r n:ℝ) ≤ scale := by simpa only [pow_one] using pow_le_pow_right₀ logs hD
  have locBound : X*scale ≤ localWork a D α ξ r n R := by
    unfold localWork
    change X*scale ≤ (X+((Routing.labelCount a α n:ℝ)+R)^10)*scale
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by dsimp [scale]; positivity)
  have charged : ((w:ℝ)+1)*X ≤ L*localWork a D α ξ r n R := calc
    _ ≤ (L*scale)*X := mul_le_mul_of_nonneg_right words xp
    _ = L*(X*scale) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left locBound hL
  have use : (positions:ℝ) ≤ localWork a D α ξ r n R := calc
    _ ≤ (r:ℝ)*(logWidth r n:ℝ) := by exact_mod_cast origin
    _ ≤ X*scale := mul_le_mul rx pow (by positivity) xp
    _ ≤ _ := locBound
  have h : (cost:ℝ) ≤ publicFactor*(((w+1)*(2^p+2^d):ℕ):ℝ)+liveFactor*(((w:ℝ)+1)*X)+useFactor*positions := by
    dsimp only [X]; exact_mod_cast physical
  have pbound := mul_le_mul_of_nonneg_left g (show 0 ≤ (publicFactor:ℝ) by positivity)
  have lbound := mul_le_mul_of_nonneg_left charged (show 0 ≤ (liveFactor:ℝ) by positivity)
  have ubound := mul_le_mul_of_nonneg_left use (show 0 ≤ (useFactor:ℝ) by positivity)
  linarith only [h,pbound,lbound,ubound]

/-- Applying the public geometry allowance and the logarithmic word-width bound to
the signed native cell clocks at the rounded exterior scale. -/
theorem signed_cell_scale (p d k u b w a D n r R : ℕ) (α ξ A L : ℝ)
    (hL : 0 ≤ L) (hn : 1 ≤ n) (hr : 1 ≤ r) (hξ : ξ ≤ 1) (hD : 1 ≤ D)
    (bw : 1 ≤ b) (ww : 1 ≤ w)
    (geo : (GeometryAdviceRate.ticks k u (Total p d) b w : ℝ) ≤ A*publicWork a α r n R)
    (words : (w:ℝ)+1 ≤ L*(logWidth r n:ℝ)^D)
    (positions : ℕ) (origin : positions ≤ r*logWidth r n) (cost : ℕ)
    (physical : cost ≤ 1200*((w+1)*(2^p+2^d)) + 700000000*((w+1)*exterior ξ r n) + 439*positions) :
    (cost : ℝ) ≤ 1200*A*publicWork a α r n R+(700000000*L+439)*localWork a D α ξ r n R := by
  simpa using cell_scale 1200 700000000 439 p d k u b w a D n r R α ξ A L hL hn hr hξ hD bw ww
    geo words positions origin cost physical
end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
