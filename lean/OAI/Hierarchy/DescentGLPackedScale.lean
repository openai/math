import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Dyadic lane width for an elementary shuffle at independent data and CPU widths -/
namespace Hierarchy.DescentGLPacked
open scoped BigOperators

def lowBits (m b data : ℕ) := min m (data/(4*b)).log2

theorem lane_fit (m b data : ℕ) (pos : 0<b) (wide : 4*b≤data) :
    (b+b)*2^lowBits m b data≤data/2 := by
  let q:=data/(4*b)
  have nonzero:q≠0:=Nat.ne_of_gt (Nat.div_pos wide (by omega))
  have K : 2^lowBits m b data≤q :=
    (Nat.pow_le_pow_right (by decide : 0<2) (min_le_right ..)).trans (Nat.log2_self_le nonzero)
  apply (Nat.le_div_iff_mul_le (by decide : 0<2)).2
  have mul:=(Nat.mul_le_mul_right (4*b) K).trans (Nat.div_mul_le_self data (4*b))
  nlinarith only [mul]

theorem block_invoice (m b data : ℕ) (pos : 0<b) (_wide : 4*b≤data) :
    let l:=lowBits m b data
    2^(m-l)*data≤data+8*2^m*b := by
  dsimp only
  by_cases short : m≤(data/(4*b)).log2
  · simp [lowBits,min_eq_left short]
  · let q:=data/(4*b)
    let l:=q.log2
    have below : l≤ m:=by change (data/(4*b)).log2≤ m;omega
    have named:lowBits m b data=l:=min_eq_right below
    have hi : q<2^(l+1):=Nat.lt_log2_self
    rw [pow_succ] at hi
    have eqn:=Nat.div_add_mod data (4*b)
    have rem:=Nat.mod_lt data (show 0<4*b by omega)
    have right : data≤(2^l)*8*b := by
      have cap := Nat.mul_le_mul_left (4*b) (Nat.succ_le_of_lt hi)
      change 4*b*q+data%(4*b)=data at eqn
      nlinarith only [cap,eqn,rem]
    have both : 2^(m-l)*2^l=2^m:=by rw [←pow_add,Nat.sub_add_cancel below]
    have cost:=Nat.mul_le_mul_left (2^(m-l)) right
    rw [named]
    nlinarith only [cost,both,congrArg (fun n:ℕ=>8*n*b) both]

theorem charged (H m b data cpu C : ℕ) (pos : 0<b) (wide : 4*b≤data) (scale : cpu≤C*data) :
    let l:=lowBits m b data
    (H*2^(m-l))*cpu≤C*(H*data+8*H*2^m*b) := by
  dsimp only
  have count:=Nat.mul_le_mul_left H (block_invoice m b data pos wide)
  have cap:=Nat.mul_le_mul_left (H*2^(m-lowBits m b data)) scale
  nlinarith only [cap,Nat.mul_le_mul_left C count]

end Hierarchy.DescentGLPacked

end OAI
