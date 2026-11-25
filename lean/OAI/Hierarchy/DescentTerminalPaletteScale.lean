import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # The fixed local palette fits after the word exponent has already been chosen -/
namespace Hierarchy.DescentCompiler.TerminalScale
open Filter

theorem linear_palette (C K B e : ℕ) (positive : 0<B) (two : 2≤e) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      C+8*(2*B*(J+1)+J*K+1)≤(2*2^J)^e := by
  let budget:=C+8*(2*B+K+1)
  filter_upwards [eventually_late budget B positive] with h age
  let J:=Nat.log 2 h/(2*B)
  have room : budget≤2^(J+1) := age.trans ((Nat.le_succ J).trans (Nat.lt_two_pow_self (n:=J+1)).le)
  have roomJ : J+1≤2^(J+1) := (Nat.lt_two_pow_self (n:=J+1)).le
  calc
    C+8*(2*B*(J+1)+J*K+1) ≤ budget*(J+1) := by dsimp [budget];nlinarith
    _ ≤ 2^(J+1)*2^(J+1) := Nat.mul_le_mul room roomJ
    _ = (2*2^J)^2 := by rw [pow_succ 2 J,pow_two];ring
    _ ≤ _ := Nat.pow_le_pow_right (by positivity) two

end Hierarchy.DescentCompiler.TerminalScale

end OAI
