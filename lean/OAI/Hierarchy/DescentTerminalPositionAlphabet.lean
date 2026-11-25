import Mathlib.Data.Nat.Log

namespace OAI
/-! # Alphabet size of the terminal position table -/
namespace Hierarchy.DescentTerminalSiteShelves
variable {V W B : ℕ}

def alphabet (V W B : ℕ) := (V+1)*((W+1)*(B*((2^B)*(2^B))))

theorem alphabet_bound (h : ℕ) (small : Nat.clog 2 (V+1)+Nat.clog 2 (W+1)+Nat.clog 2 B+2*B≤h/2) :
    alphabet V W B≤2^(h/2) := by
  have cap (n : ℕ) : n≤2^(Nat.clog 2 n):=Nat.le_pow_clog (by decide) n
  have bound:=Nat.mul_le_mul (cap (V+1)) (Nat.mul_le_mul (cap (W+1)) (Nat.mul_le_mul (cap B) (le_refl ((2^B)*(2^B)))))
  unfold alphabet
  apply bound.trans
  simp only [←Nat.pow_add]
  exact Nat.pow_le_pow_right (by decide) (by omega)

end Hierarchy.DescentTerminalSiteShelves

end OAI
