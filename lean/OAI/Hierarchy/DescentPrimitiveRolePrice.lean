import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI
/-! # Encoded scalar tag widths at the compiler's logarithmic height -/
namespace Hierarchy.DescentPrimitiveRolePrice

theorem payload (h B p : ℕ) (hp : p≤h) (hb : 0<B) :
    p≤2^(2*B*(Nat.log 2 h/(2*B)+1)) := by
  have hb' : 0<2*B := by omega
  have q := (Nat.div_lt_iff_lt_mul hb').mp (Nat.lt_succ_self (Nat.log 2 h/(2*B)))
  have hlog : Nat.log 2 h+1 ≤ 2*B*(Nat.log 2 h/(2*B)+1) := by
    simpa [Nat.mul_comm] using q
  exact hp.trans ((Nat.lt_pow_succ_log_self (by decide) h).le.trans (Nat.pow_le_pow_right (by decide) hlog))

/-- The exponent holding the price constant is independent of the parameter B.
Only the coefficient of J in the displayed bound depends on B. -/
theorem tagBits {colors seed C J B p h g : ℕ} (hb : 0<B) (chosen : J=Nat.log 2 h/(2*B))
    (word : p≤h) (grain : seed≤p*(2^J)^g)
    (alphabet : colors≤C*(seed+1)^8) :
    Nat.clog 2 (colors+1) ≤ Nat.clog 2 (C+1)+8*(2*B*(J+1)+J*g+1) := by
  apply (Nat.clog_le_iff_le_pow (by decide)).2
  let q:=2*B*(J+1)
  have packed : p≤2^q := by dsimp [q];rw [chosen];exact payload h B p word hb
  have sw : seed≤2^(q+J*g) := by
    calc
      _ ≤ p*(2^J)^g := grain
      _ ≤ 2^q*(2^J)^g := Nat.mul_le_mul_right _ packed
      _ = _ := by rw [pow_add,pow_mul (2:ℕ) J g]
  have sp : seed+1≤2^(q+J*g+1) := by rw [pow_succ];have := Nat.two_pow_pos (q+J*g);omega
  have eight : (seed+1)^8≤2^(8*(q+J*g+1)) := by
    rw [Nat.mul_comm 8 _,pow_mul];exact Nat.pow_le_pow_left sp _
  have const := Nat.le_pow_clog (by decide : 1<2) (C+1)
  have mass:=alphabet.trans (Nat.mul_le_mul_left C eight)
  have whole : colors+1≤(C+1)*2^(8*(q+J*g+1)) := by
    rw [Nat.add_mul,Nat.one_mul];exact Nat.add_le_add mass (Nat.two_pow_pos _)
  rw [pow_add]
  exact whole.trans (Nat.mul_le_mul_right _ const)

end Hierarchy.DescentPrimitiveRolePrice

end OAI
