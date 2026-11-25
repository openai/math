import OAI.Computability.NearSquareRoot.PrecisionPieceTrajectory
import OAI.Computability.NearSquareRoot.PrecisionPieceSize
import OAI.Computability.NearSquareRoot.PrecisionRecursiveWalsh

/-! # Admissibility and error of the executed even Walsh schedule

The template and plan are fixed before the grid width is chosen. The uniform
threshold works for all selected widths and all represented padded inputs
in the multiplication transform's working range.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces
open Filter IntegerMultiplication KernelPass PhysicalWalshNode FlatWalshNode FixedPoint

noncomputable section

/-- The full physical interval occupied by the nonzero recursion pieces,
including any extra spectator rows for fanout alignment. -/
abbrev evenTarget (s : ℕ) (y : IdealRow) := activeRow (2*(s/2)) (2^(s%2)) y

/-- Pointwise numerical certificate at address width `k`. -/
def EvenAccurateAt {a W : ℕ} (ha : 1<a+1) (hw : 0<W) (plan : Plan (a+1) W W) (k : ℕ) : Prop :=
  ∀ s ≤ k, ∀ x : ℕ → Record k,
    let b := Root.mk k s (componentBits k) x
    let N := extent (a+1) W k s
    let start := decoded (fractionBits k) x
    ‖atWidth N start‖ ≤ (2:ℝ)^(13*k) →
    b.Feasible hw plan ha ∧ ‖atWidth N (evenTarget s start)‖ = ‖atWidth N start‖ ∧
      ‖atWidth N (decoded (fractionBits k)
        (b.stage hw plan (b.pieces (a:=a) hw).length)) - atWidth N (evenTarget s start)‖ ≤
        1/(2:ℝ)^(67*k)

theorem even_accurate_of_bounds {a W k : ℕ} (ha : 1<a+1) (hw : 0<W) (plan : Plan (a+1) W W)
    (hk : 1 ≤ k)
    (node : RunAccurateAt hw plan k) (volume : ∀ s ≤ k, extent (a+1) W k s ≤ 2^(2*k)) :
    EvenAccurateAt ha hw plan k := by
  intro s hs x b N start hin
  let l := b.pieces (a:=a) hw
  have hl : l.length ≤ k := (schedule_length_le ha hw k s _).trans hs
  have small : (l.length:ℝ) * (1/(2:ℝ)^(68*k)) ≤ 1/(2:ℝ)^(67*k) := by
    have hn : l.length ≤ 2^k := hl.trans (Nat.lt_two_pow_self (n:=k)).le
    have hn' : (l.length:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast hn
    calc
      _ ≤ (2:ℝ)^k * (1/2^(68*k)) := mul_le_mul_of_nonneg_right hn' (by positivity)
      _ = _ := by rw [show 68*k=67*k+k by omega,pow_add]; field_simp
  have hR : ‖atWidth N start‖ + (l.length:ℝ) * (1/(2:ℝ)^(68*k)) ≤ (2:ℝ)^(17*k) := by
    have unit : 1/(2:ℝ)^(67*k) ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
    calc
      _ ≤ (2:ℝ)^(13*k)+1 := add_le_add hin (small.trans unit)
      _ ≤ (2:ℝ)^(13*k+1) := by rw [pow_succ]; linarith [one_le_pow₀ (by norm_num : 1 ≤ (2:ℝ)) (n:=13*k)]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  obtain ⟨fit,isom,gap⟩ := trajectory_bound ha hw plan b (fractionBits k) (by positivity) hR (by
    intro j u y ready
    have g := get_geometry hw ha k s (componentBits k) j
    exact node u g.1 g.2.2 ((level_pow_le ha hw (List.get_mem _ j)).trans hs)
      (g.2.1.trans_le (volume s hs)) y ready)
  exact ⟨fit,isom,gap.trans small⟩

theorem eventually_even_accurate {a W : ℕ} (ha : 1<a+1) (hw : 0<W) (plan : Plan (a+1) W W)
    (hp : Correct plan) : ∀ᶠ k : ℕ in atTop, EvenAccurateAt ha hw plan k := by
  filter_upwards [eventually_run_good hw plan hp, eventually_extent_le ha hw, eventually_ge_atTop (1:ℕ)] with k node volume hk
  exact even_accurate_of_bounds ha hw plan hk node volume

end
end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
