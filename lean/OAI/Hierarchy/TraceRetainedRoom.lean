import Mathlib.Tactic

namespace OAI
/-! # Word bounds for the native graph and width metadata writers -/

namespace Hierarchy.TraceRetainedRoom

/-- A stage uses at most `q` rows or fixed table entries.  Its layout score,
including multiplicities and the square of the propagated wire width, fits a word. -/
structure Room (q W : ℕ) : Prop where
  table : 80 ≤ q
  capacity : q^12 < 2^W

theorem native {w : ℕ} (enough : 7 ≤ w) : Room (2^w) (64*w) := by
  constructor
  · exact (by decide : 80 ≤ 2^7).trans (Nat.pow_le_pow_right (by decide) enough)
  · rw [←pow_mul]
    exact Nat.pow_lt_pow_right (by decide) (by omega)

theorem Room.power {q W j : ℕ} (h : Room q W) (jle : j ≤ 12) : q^j < 2^W := by
  exact (Nat.pow_le_pow_right (by have := h.table; omega) jle).trans_lt h.capacity

theorem Room.single {q W : ℕ} (h : Room q W) : q < 2^W := by
  simpa only [pow_one] using h.power (by decide : 1 ≤ 12)

theorem Room.square {q W : ℕ} (h : Room q W) : q*q < 2^W := by
  simpa only [pow_two] using h.power (by decide : 2 ≤ 12)

/-- Widths of old thick bundles, widths of selected successors, and the exact
integer score used in the binary layout comparison all fit simultaneously. -/
theorem Room.measured {q W : ℕ} (room : Room q W) {rows factor mult base width : ℕ}
    (rowCount : rows ≤ q) (factorCap : factor ≤ q) (multCap : mult ≤ q)
    (baseCap : base ≤ q) (oldWidth : width+1 ≤ q^4) :
    1+2*(mult*width)+base < 2^W ∧ factor*(1+width) < 2^W ∧
      80*rows*(factor*(1+width))^2 < 2^W := by
  have fixed := room.table
  have old : width ≤ q^4 := by omega
  have thick : mult*width ≤ q^5 := calc
    _ ≤ q*q^4 := Nat.mul_le_mul multCap old
    _ = _ := by ring
  have issued : factor*(1+width) ≤ q^5 := calc
    _ ≤ q*q^4 := Nat.mul_le_mul factorCap (by omega)
    _ = _ := by ring
  have baseBig : q ≤ q^5 := Nat.le_self_pow (by decide) _
  have sum : 1+2*(mult*width)+base ≤ q^6 := calc
    _ ≤ 4*q^5 := by omega
    _ ≤ q*q^5 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring
  have score : 80*rows*(factor*(1+width))^2 ≤ q^12 := calc
    _ ≤ (q*q)*(q^5)^2 := Nat.mul_le_mul (Nat.mul_le_mul fixed rowCount)
      (Nat.pow_le_pow_left issued _)
    _ = _ := by ring
  exact ⟨sum.trans_lt (room.power (by decide)), issued.trans_lt (room.power (by decide)),
    score.trans_lt room.capacity⟩

end Hierarchy.TraceRetainedRoom

end OAI
