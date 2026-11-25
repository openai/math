import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! The simultaneous approximation and stability estimates used in Appendix A. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

/-- Pigeonholing the first `Q ^ p + 1` multiples in the `Q ^ p` fractional-part boxes.
The same positive multiplier works for every coordinate, including irrational coordinates. -/
theorem simultaneous_dirichlet {p Q : ℕ} (hQ : 0 < Q) (u : Fin p → ℝ) :
    ∃ q : ℕ, 0 < q ∧ q ≤ Q ^ p ∧ ∃ z : Fin p → ℤ,
      ∀ i, |(q : ℝ) * u i - z i| ≤ 1 / (Q : ℝ) := by
  have hQ' : 0 < (Q : ℝ) := by exact_mod_cast hQ
  let pos (k : ℕ) (i : Fin p) := (Q : ℝ) * Int.fract ((k : ℝ) * u i)
  have hpos (k : ℕ) (i : Fin p) : 0 ≤ pos k i :=
    mul_nonneg hQ'.le (Int.fract_nonneg _)
  let cell (k : Fin (Q ^ p + 1)) (i : Fin p) : Fin Q :=
    ⟨⌊pos k i⌋₊, (Nat.floor_lt (hpos _ _)).2 (mul_lt_of_lt_one_right hQ' (Int.fract_lt_one _))⟩
  obtain ⟨x, y, hne, hxy⟩ := Fintype.exists_ne_map_eq_of_card_lt cell (by simp)
  obtain ⟨x, y, hlt, heq⟩ : ∃ x y : Fin (Q ^ p + 1), x < y ∧ cell x = cell y := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨x, y, h, hxy⟩
    · exact ⟨y, x, h, hxy.symm⟩
  have hle : x.val ≤ y.val := hlt.le
  refine ⟨y.val - x.val, Nat.sub_pos_of_lt hlt,
    (Nat.sub_le ..).trans (Nat.le_of_lt_succ y.isLt),
    fun i ↦ ⌊(y.val : ℝ) * u i⌋ - ⌊(x.val : ℝ) * u i⌋, ?_⟩
  intro i
  have hc : ⌊pos y.val i⌋₊ = ⌊pos x.val i⌋₊ := congrArg Fin.val (congrFun heq.symm i)
  have h1 := Nat.floor_le (hpos x.val i)
  have h2 := Nat.floor_le (hpos y.val i)
  have h3 := Nat.lt_floor_add_one (pos x.val i)
  have h4 := Nat.lt_floor_add_one (pos y.val i)
  rw [hc] at h2 h4
  have diff : |pos y.val i - pos x.val i| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [le_div_iff₀ hQ', ← abs_of_pos hQ', ← abs_mul]
  convert diff using 2
  simp only [pos, Int.fract, Nat.cast_sub hle, Int.cast_sub]
  ring

/-- Transfer the approximation of the dyadic oracle answer to the underlying real input. -/
theorem simultaneous_approximation_stable {p : ℕ} (u u' : Fin p → ℝ)
    (z : Fin p → ℤ) (q : ℕ) (α ε : ℝ)
    (hα : ∀ i, |u i - u' i| ≤ α) (hq : (q : ℝ) * α ≤ ε / 2)
    (hz : ∀ i, |(q : ℝ) * u' i - z i| ≤ ε / 2) :
    ∀ i, |(q : ℝ) * u i - z i| ≤ ε := by
  intro i
  calc
    |(q : ℝ) * u i - z i| = |q * (u i - u' i) + (q * u' i - z i)| := by congr 1; ring
    _ ≤ |(q : ℝ) * (u i - u' i)| + |q * u' i - z i| := abs_add_le ..
    _ = q * |u i - u' i| + |q * u' i - z i| := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg q)]
    _ ≤ ε / 2 + ε / 2 := add_le_add ((mul_le_mul_of_nonneg_left (hα i) (Nat.cast_nonneg q)).trans hq) (hz i)
    _ = ε := by ring

end Lattice
end LinearProgramming
end Optimization
end OAI
