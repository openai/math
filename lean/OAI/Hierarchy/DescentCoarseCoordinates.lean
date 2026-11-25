import OAI.Hierarchy.DescentColonyLayout

namespace OAI
/-! # The low and high fields of the reset's dyadic coordinate -/

namespace Hierarchy.DescentIssuedFallbackPanel
open DescentColonies
variable {m c : ℕ} (fits : c≤m)
def join (hi : Block c) (lo : Fin (2^(m-c))) : Block m :=
  ⟨hi.val*2^(m-c)+lo.val,by
    calc
      _<hi.val*2^(m-c)+2^(m-c):=Nat.add_lt_add_left lo.isLt _
      _=(hi.val+1)*2^(m-c):=(Nat.succ_mul ..).symm
      _≤(2^c)*2^(m-c):=Nat.mul_le_mul_right _ hi.isLt
      _=2^m:=by rw [←pow_add,Nat.add_sub_of_le fits]⟩

end Hierarchy.DescentIssuedFallbackPanel

namespace Hierarchy.DescentPlainTerminal
open DescentColonies DescentIssuedFallbackPanel
variable {m c : ℕ} (small : c≤m)
def high (y : Block m) : Block c := ⟨group c y,by
  change y.val/2^(m-c)<2^c
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
  simpa only [←Nat.pow_add,Nat.add_sub_of_le small] using y.isLt⟩

def low (y : Block m) : Block (m-c) := ⟨y.val%2^(m-c),Nat.mod_lt _ (Nat.two_pow_pos _)⟩

@[simp] theorem high_join (a : Block c) (j : Block (m-c)) : high small (join small a j)=a := by
  apply Fin.ext
  change (a.val*2^(m-c)+j.val)/2^(m-c)=a.val
  rw [Nat.mul_comm a.val (2^(m-c)),Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt j.isLt,Nat.add_zero]

@[simp] theorem low_join (a : Block c) (j : Block (m-c)) : low (join small a j)=j := by
  apply Fin.ext
  change (a.val*2^(m-c)+j.val)%2^(m-c)=j.val
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt j.isLt]

@[simp] theorem join_high_low (y : Block m) : join small (high small y) (low y)=y := by
  apply Fin.ext
  change y.val/2^(m-c)*2^(m-c)+y.val%2^(m-c)=y.val
  exact Nat.div_add_mod' ..

end Hierarchy.DescentPlainTerminal

end OAI
