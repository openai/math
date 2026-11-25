import OAI.ThreeFlat.Diagonal.PhysicalStage
import OAI.Computability.VPVNP.Compression

namespace OAI
/-! # A halving bound for the energy and size of a physical state -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression
open scoped BigOperators

/-- A quarter-step in energy, with quadratic position error, and a
fourfold decrease in positions halve the stated potential together. -/
theorem potential_half {E E' P P' c : ℝ} (hE : 0 ≤ E) (hP : 0 ≤ P) (hc : 0 ≤ c)
    (energy : E' ≤ E/4+c*P^2) (positions : 4*P' ≤ P) :
    Real.sqrt E' + (4*Real.sqrt c)*P' ≤ (Real.sqrt E + (4*Real.sqrt c)*P)/2 := by
  have root : Real.sqrt E' ≤ Real.sqrt E/2 + Real.sqrt c*P := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, energy.trans ?_⟩
    rw [add_sq, div_pow, mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hc]
    have cross := mul_nonneg (Real.sqrt_nonneg E) (mul_nonneg (Real.sqrt_nonneg c) hP)
    linarith only [cross]
  have reduced := mul_le_mul_of_nonneg_left positions (Real.sqrt_nonneg c)
  linarith only [root,reduced]

def State.widthSum {d l : ℕ} (A : State d l) : ℕ := ∑ e, A.width e

/-- A state's wire indices have total uniform mass one, so their total
physical width is at most the square root of the displayed energy. -/
theorem State.widthSum_le_sqrt_energy {d l : ℕ} (A : State d l) (hd : 0<d) :
    (A.widthSum : ℝ) ≤ Real.sqrt A.energy := by
  have site : A.positions = Fintype.card A.Base * Fintype.card (BitWord l) :=
    (Fintype.card_congr A.chart).symm.trans (Fintype.card_prod _ _)
  have card : Fintype.card ((A.Base × Fin d) × BitWord l) = A.positions*d := by
    simp only [site,Fintype.card_prod,Fintype.card_fin]
    ring
  have positive : 0 < A.positions := by rw [site]; exact Nat.mul_pos Fintype.card_pos Fintype.card_pos
  have hp : (0:ℝ) < (A.positions:ℝ)*d := by positivity
  have unit : ∑ _ : (A.Base × Fin d) × BitWord l, (1 / ((A.positions:ℝ)*d)) = 1 := by
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card,Nat.cast_mul,mul_one_div,div_self hp.ne']
  simpa only [State.widthSum, Nat.cast_sum, State.energy] using
    (Computability.VPVNP.Compression.widthSum_le_sqrtEnergy (fun e => (A.width e : ℝ)) (fun _ => 1/((A.positions:ℝ)*d))
      (fun _ => one_div_pos.mpr hp) unit)

end ThreeFlat.Diagonal.PhysicalStage

end
end OAI
