import OAI.Hierarchy.DescentTerminalFieldSize
import OAI.Hierarchy.DescentTerminalScalarHeader

namespace OAI
/-! # Storage and decoder range of a terminal scalar row -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalControlBits
noncomputable section
variable (q t H N A p V W B h:ℕ)
local notation "s" => span q t H N A p
local notation "tag" => Nat.clog 2 (t+1)
local notation "r" => rowBits q tag H N A p V
local notation "num" => DescentTerminalScalarHeader.range q t H N A p V

theorem row_storage (roles:0<t) : r≤Nat.clog 2 (V+1)+2*(V*s) := by
  have high:t+1≤2^tag:=Nat.le_pow_clog (by decide) _
  have one:1≤tag:=by
    by_contra! x
    have eqn:tag=0:=by omega
    rw [eqn,pow_zero] at high;omega
  have nodes:N≤N*tag:=Nat.le_mul_of_pos_right _ one
  have inside:bookBits q tag H N A p≤2*s:=by
    rw [size]
    simp only [bookBits,nodeBits,lg,Nat.mul_add,Nat.mul_assoc,Nat.mul_one] at *
    omega
  have scale:=Nat.mul_le_mul_left V inside
  unfold rowBits
  rw [show V*(2*s)=2*(V*s) by ring] at scale
  exact Nat.add_le_add_left scale _

/-- The same physical bound on all nine fields bounds the range of the literal row decoder. -/
theorem scalar_range (roles : 0<t) (page : 32*(V*s) ≤ h) (large : 10 ≤ h) :
    num+1 ≤ 2^(h/2) := by
  have positive : 0 < s := by rw [size]; omega
  have sites : V ≤ V*s := Nat.le_mul_of_pos_right V positive
  have width : Nat.clog 2 (V+1) ≤ V :=
    (Nat.clog_le_iff_le_pow (by decide)).mpr Nat.lt_two_pow_self
  have rsize := row_storage q t H N A p V roles
  have budget : r+1 ≤ h/2 := by omega
  have tagFit : t ≤ 2^tag := (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have rangeFit := DescentTerminalScalarHeader.header_room q t H N A p V tag tagFit
  have extra : num+1 ≤ 2^(r+1) := by rw [pow_succ]; have := Nat.two_pow_pos r; omega
  exact extra.trans (Nat.pow_le_pow_right (by decide) budget)

end
end Hierarchy.DescentTerminalVertexFields

end OAI
