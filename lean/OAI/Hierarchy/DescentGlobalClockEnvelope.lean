import Mathlib.Tactic

namespace OAI
/-! # Explicit bound for the combined matrix-search and permutation clocks -/
namespace Hierarchy.DescentCompiler

theorem global_clock_envelope (m : ℕ) :
    4+2^m*16+m*(3200*(m+1)*2^(3*m))+
      (4+2^m*(2*(1+m*(2+2^m*(9+5*2^m)))+4)) ≤ 4000*2^(5*m) := by
  let Z:=2^m
  have pos : 1≤Z := Nat.two_pow_pos m
  have inc : m+1≤Z := Nat.lt_pow_self (n:=m) (a:=2) (by decide)
  have mZ : m≤Z := (Nat.le_succ _).trans inc
  have triple : 2^(3*m)=Z^3 := by dsimp only [Z];rw [Nat.mul_comm 3,pow_mul]
  have five : Z^5=2^(5*m) := by dsimp only [Z];rw [Nat.mul_comm 5,pow_mul]
  rw [triple,←five]
  change 4+Z*16+m*(3200*(m+1)*Z^3)+(4+Z*(2*(1+m*(2+Z*(9+5*Z)))+4))≤_
  calc
    _ ≤ 4+Z*16+Z*(3200*Z*Z^3)+(4+Z*(2*(1+Z*(2+Z*(9+5*Z)))+4)) := by
      gcongr
    _ ≤ 4000*Z^5 := by
      have p0:=Nat.one_le_pow 5 Z pos
      have p1 : Z≤Z^5 := Nat.le_self_pow (by decide) Z
      have p2:=Nat.pow_le_pow_right pos (show 2≤5 by decide)
      have p3:=Nat.pow_le_pow_right pos (show 3≤5 by decide)
      have p4:=Nat.pow_le_pow_right pos (show 4≤5 by decide)
      nlinarith only [p0,p1,p2,p3,p4]

end Hierarchy.DescentCompiler

end OAI
