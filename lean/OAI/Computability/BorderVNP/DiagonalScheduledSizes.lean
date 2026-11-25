import OAI.Computability.BorderVNP.DiagonalStretchAssembly
import OAI.Computability.BorderVNP.TeamContractionWireScale

/-! # Physical sizes of the fixed diagonal processor program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales TeamContraction
open scoped Classical

/-- The actual §7 RAM address logarithm is controlled by the branch advice
scale even when the batch size is stretched exponential. -/
theorem logWidth_le_adviceScale (σ ρ : ℝ) (n : ℕ) :
    logWidth (stretch ρ n) n ≤ adviceScale σ ρ n + 1 := by
  let r := stretch ρ n
  have hlog : logWidth r n = Nat.clog 2 (2*n*r) := by
    unfold logWidth
    rw [← Real.natCeil_logb_natCast]
    norm_cast
  change logWidth r n ≤ _
  rw [hlog]
  refine (Nat.clog_le_of_le_pow (show 2*n*r ≤ 2^(1+n+Nat.clog 2 (r+1)) from ?_)).trans ?_
  · rw [pow_add,pow_add,pow_one]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 Nat.lt_two_pow_self.le)
      ((Nat.le_succ r).trans (Nat.le_pow_clog (by decide) _))
  · unfold adviceScale
    dsimp [r]
    omega

/-- A concrete schedule uses the source team count and exterior width,
logarithmic-power counter words, and the actual sorter and state-frame
wire names. Register count and all powers are fixed by the program. -/
noncomputable def physicalSchedule {σ ρ α τ : ℝ} (hσ : 0 < σ) (hσρ : σ < ρ)
    (K : ℕ) (hK : 1 ≤ K) (hτ : 0 ≤ τ) (hg : τ * Real.logb 2 K ≤ α)
    (hα : 2*α ≤ 1) (reg wordDegree tallyDegree multDegree : ℕ) : StretchSchedule where
  σ := σ
  ρ := ρ
  positive := hσ
  separated := hσρ
  teamsPred n := teams α τ K n - 1
  link n := TeamScales.link (τ/5) (teams α τ K n) n
  word n := logWidth (stretch ρ n) n ^ wordDegree
  tally n := logWidth (stretch ρ n) n ^ tallyDegree
  multBits n := logWidth (stretch ρ n) n ^ multDegree
  Edge n := let r := stretch ρ n
            let w := logWidth r n ^ wordDegree
            Wires.Edge r reg w (Wires.sortExponent (block (τ/5) n)) (w+1)
  resources := by
    let d := max 1 (max wordDegree (max tallyDegree multDegree))
    refine ⟨4,d,?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    let M := adviceScale σ ρ n + 1
    have hM : 0 < M := Nat.succ_pos _
    have hlength : n < M := by dsimp [M,adviceScale]; omega
    have hnreal : 1 ≤ (n:ℝ) := by exact_mod_cast hn
    have htReal : (teams α τ K n : ℝ) ≤ n := (teams_le hK hn hτ hg).trans
      ((Real.rpow_le_rpow_of_exponent_le hnreal hα).trans_eq (Real.rpow_one _))
    have ht : teams α τ K n ≤ n := by exact_mod_cast htReal
    have hp (j : ℕ) (hj : j ≤ d) : logWidth (stretch ρ n) n ^ j ≤ M ^ d :=
      (Nat.pow_le_pow_left (logWidth_le_adviceScale σ ρ n) _).trans (Nat.pow_le_pow_right hM hj)
    have hw := hp wordDegree (by dsimp [d]; omega)
    have hcount := hp multDegree (by dsimp [d]; omega)
    have htot := hp tallyDegree (by dsimp [d]; omega)
    have hMp : M ≤ M^d := Nat.le_self_pow (by dsimp [d]; omega) _
    change teams α τ K n - 1 + 1 + _ + _ + _ ≤ 4*M^d
    omega

/-- On every positive length, the public schedule has exactly the stated
number of teams, including the floor in the initial copy multiplicity. -/
theorem physicalSchedule_teams {σ ρ α τ : ℝ} (hσ : 0 < σ) (hσρ : σ < ρ)
    (K : ℕ) (hK : 1 ≤ K) (hτ : 0 ≤ τ) (hg : τ * Real.logb 2 K ≤ α)
    (ha : 0 ≤ α) (hα : 2*α ≤ 1) (reg wordDegree tallyDegree multDegree : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    (physicalSchedule hσ hσρ K hK hτ hg hα reg wordDegree tallyDegree multDegree).teamsPred n + 1 =
      teams α τ K n := by
  apply Nat.sub_add_cancel
  apply Nat.one_le_iff_ne_zero.mpr
  unfold teams
  have hw : 1 ≤ width n α := by
    apply Nat.le_floor
    simpa using Real.one_le_rpow (by exact_mod_cast hn : (1:ℝ) ≤ n) ha
  exact Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))

end Diagonal

end BorderVNP
end Computability
end OAI
