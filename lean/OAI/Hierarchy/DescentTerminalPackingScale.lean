import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # The exact integer quantum used in the terminal population reserve -/
namespace Hierarchy.DescentCompiler.TerminalScale

theorem floor_scale (h U q J a e : ℕ) (hU : 0<U) (hq : 0<q) (large : 32*(q*U)≤h)
    (socket : q≤scale J a) (shrink : U≤scale J e) :
    let p:=h/(16*(q*U)); let p₀:=p*U
    0<p ∧ 16*(q*p₀)≤h ∧ h≤32*(q*p₀) ∧ h≤p*scale J (5+a+e) := by
  obtain ⟨pos,_,lower,upper⟩:=packing_width hU hq large
  refine ⟨pos,lower,upper,upper.trans ?_⟩
  have c : 32≤scale J 5 := by
    change 2^5≤2^(5*(J+1))
    exact Nat.pow_le_pow_right (by decide) (by omega)
  rw [←scale_mul,←scale_mul]
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using
    Nat.mul_le_mul_left (h/(16*(q*U))) (Nat.mul_le_mul (Nat.mul_le_mul c socket) shrink)

theorem floor_reserve (h U q J a e c d s τ cost : ℕ) (hU : 0<U) (hq : 0<q)
    (large : 32*(q*U)≤h) (socket : q≤scale J a) (shrink : U≤scale J e)
    (late : c*(τ+1)^d≤2^(J+1)) (enough : s+(d+1)+(5+a+e)≤τ)
    (shared : cost≤scale J s*(c*(tail τ J+1)^d)) :
    cost*h≤(h/(16*(q*U)))*2^(tail τ J) :=
  reserve c d s (5+a+e) τ J cost h _ late enough shared
    (floor_scale h U q J a e hU hq large socket shrink).2.2.2

end Hierarchy.DescentCompiler.TerminalScale

end OAI
