import OAI.ThreeFlat.Diagonal.TickScratchRegion
import OAI.ThreeFlat.Diagonal.TickGreedyWord
import Mathlib.Tactic.Positivity

namespace OAI
/-! # Disjoint regions of the native tick's external scratch memory -/

namespace ThreeFlat.Diagonal.TickWorkspace

theorem lower (u i : ℕ) : stride u ≤ base u i := by
  unfold base
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem apart {u i j : ℕ} (h : i<j) : base u i+stride u ≤ base u j := by
  change (i+1)*stride u+stride u ≤ (j+1)*stride u
  rw [← Nat.succ_mul]
  exact Nat.mul_le_mul_right _ (by omega)

theorem ordered {u i j x y : ℕ} (h : i<j) (hx : x<stride u) :
    base u i+x < base u j+y := by have := apart (u:=u) h; omega

theorem word_space {u i : ℕ} (hu : 1 ≤ u) (hi : i < stride u) :
    base u i+stride u < 2^(16*u^10) := by
  let V := 2^(u^10)
  have pos : 2 ≤ V := by
    change 2^1 ≤ 2^(u^10)
    exact Nat.pow_le_pow_right (by decide) (Nat.one_le_pow _ _ hu)
  have hstep : base u i+stride u ≤ V^4*V^4+V^4 := by
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hi) _
  have v4 : 2 ≤ V^4 := (Nat.le_self_pow (by decide : 4≠0) V).trans' pos
  have room : V^4*V^4+V^4 < (V^4*V^4)*(V^4*V^4) := by
    nlinarith [Nat.mul_le_mul_left (V^4) v4]
  have eq : (V^4*V^4)*(V^4*V^4) = 2^(16*u^10) := by
    change (((2^(u^10))^4)*((2^(u^10))^4))*(((2^(u^10))^4)*((2^(u^10))^4)) = _
    simp only [← pow_add, ← Nat.pow_mul]
    congr 1
    ring
  exact hstep.trans_lt (room.trans_eq eq)

/-- With H hidden words, J factor rows and q² field products, the entire
contraction footprint remains in the low data region. -/
theorem low_frame {u p H J q : ℕ} (hu : 16 ≤ u)
    (pins : p ≤ 2^(u^10)) (hidden : H ≤ 2^(u^10))
    (cells : J ≤ 2^(u^10)) (field : q*q ≤ 2^(u^10)) :
    2+p+H+11*J+q*q < stride u := by
  let V := 2^(u^10)
  have base16 : 16 ≤ V := by
    have := Nat.le_self_pow (by decide : 10 ≠ 0) u
    exact hu.trans (this.trans Nat.lt_two_pow_self.le)
  change _ < V^4
  change p≤V at pins
  change H≤V at hidden
  change J≤V at cells
  change q*q≤V at field
  nlinarith [Nat.mul_le_mul_left V base16, Nat.pow_le_pow_right (by omega : 0<V) (by decide : 2 ≤ 4)]

end ThreeFlat.Diagonal.TickWorkspace

end OAI
