import OAI.Hierarchy.DescentMatcherRatePolynomials
import OAI.Hierarchy.DescentCensusLaneNumbers
import OAI.Hierarchy.DescentPackedPhasePrice
import OAI.Hierarchy.DescentPackedCensusRAM

namespace OAI
/-! # The same vector lanes for the predecessor census and the ordinary chooser -/
namespace Hierarchy.DescentPackedColony.Phase
open DescentSIMDLookup DescentSixParty DescentColonies
noncomputable section

def usedBits (k b cap h : ℕ) := 2*unit k b*lanes h (recordWidth k b cap)

theorem recordWidth_polynomial (k b quota : ℕ) :
    recordWidth k b quota≤5*(1+k+b+quota)*(2^k+1) := by
  unfold recordWidth unit
  apply max_le <;> ring_nf <;> omega

theorem used_lanes (k b cap h : ℕ) : lanes (usedBits k b cap h) (unit k b)=lanes h (recordWidth k b cap) := by
  have pos : 0<2*unit k b := by dsimp [unit];omega
  exact Nat.mul_div_cancel_left _ pos

theorem used_bounds (k b cap h : ℕ) (wide : 2*recordWidth k b cap≤h) :
    2*unit k b≤usedBits k b cap h ∧ usedBits k b cap h≤h := by
  have ua : 0<unit k b := by dsimp [unit];omega
  have ra : 0<recordWidth k b cap := ua.trans_le (le_max_left ..)
  have lane := (occupancy h _ ra wide).1
  refine ⟨Nat.le_mul_of_pos_right _ lane,?_⟩
  have le' := Nat.mul_le_mul_left 2 (le_max_left (unit k b) ((1+b+2*cap)*2^k))
  exact (Nat.mul_le_mul_right _ le').trans (by
    change 2*recordWidth k b cap*(h/(2*recordWidth k b cap))≤h
    simpa [Nat.mul_comm] using Nat.div_mul_le_self h (2*recordWidth k b cap))

/-- A width-independent census scan and the entire computed chooser both
retain the first-minimum tariff at the common lane width. -/
theorem census_phase_bill_at_unit (k h w K Δ H C shared : ℕ) (L : Shelves k Δ)
    (first second : Banks) (p : 0<shared) (wide : 2*shared≤h) (hardware : w≤K*h) :
    let a:=shared
    let M:=lanes h a
    (PackedCensus.clocks first second H C M + cost L w H C M)*w ≤
      K*((96+factor k Δ)*(h+H*h+4*H*C*a)) := by
  let a:=shared
  let M:=lanes h a
  let A:=h+H*h+4*H*C*a
  let n:=H*chunks C M
  have vol : n*h≤A := (volume H C h a p wide).trans (by dsimp [A];omega)
  have hh : h≤A := by dsimp [A];omega
  have c : PackedCensus.clocks first second H C M*h ≤ 96*A := by
    simp only [PackedCensus.clocks,lookup_work]
    change (4+n*(2*20+4)+(4+n*(2*20+4)))*h≤96*A
    nlinarith only [vol,hh]
  have ss := DescentPackedMinimum.bit_price L.split h a H C p wide
  have cs := DescentPackedMinimum.bit_price L.color h a H C p wide
  have win := PackedWinnerRAM.bit_price_at k h L.paintTable L.output H C L.mu L.paint a L.panels p wide
  have ss' := AllSeeds.bit_price L.layers h H C k a p wide
  have gather : (4+n*(2*(1+33*(2^k-1))+4))*h≤(8+2*(1+33*(2^k-1)))*A := by
    calc
      _ =4*h+n*h*(2*(1+33*(2^k-1))+4) := by ring
      _ ≤4*A+A*(2*(1+33*(2^k-1))+4) := by gcongr
      _ =_ := by ring
  have phase : cost L w H C M*h ≤ factor k Δ*A := by
    rw [cost_width L w h]
    simpa only [cost,PackedChoices.ticks,factor,A,n,M,a,Nat.add_mul] using
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ss' ss) gather) cs) win
  apply DescentPackedPayloadBudget.clock hardware
  simpa only [Nat.add_mul] using Nat.add_le_add c phase

theorem census_phase_bill (k b cap h w K Δ H C : ℕ) (L : Shelves k Δ)
    (first second : Banks) (wide : 2*recordWidth k b cap≤h) (hardware : w≤K*h) :
    let a:=recordWidth k b cap
    let M:=lanes h a
    (PackedCensus.clocks first second H C M + cost L w H C M)*w ≤
      K*((96+factor k Δ)*(h+H*h+4*H*C*a)) := by
  exact census_phase_bill_at_unit k h w K Δ H C _ L first second
    ((show 0<unit k b by dsimp [unit];omega).trans_le (le_max_left ..)) wide hardware

end
end Hierarchy.DescentPackedColony.Phase

end OAI
