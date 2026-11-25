import OAI.Hierarchy.DescentTerminalFieldSize
import OAI.Hierarchy.DescentBundleTagKeys

namespace OAI
/-! # The true immutable primitive dictionary and bounded bundle-slice metadata in the field bill -/
namespace Hierarchy.DescentTerminalVertexFields
noncomputable section
variable {q H N A p T s coeff seed palette arity slices drift : ℕ}

theorem palette_clog (bill : palette≤coeff*(seed+1)^8) :
    Nat.clog 2 palette≤Nat.clog 2 coeff+8*Nat.clog 2 (seed+1) := by
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  rw [pow_add,Nat.mul_comm 8 _,pow_mul]
  exact bill.trans (Nat.mul_le_mul (Nat.le_pow_clog (by decide) coeff)
    (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) (seed+1)) 8))

private theorem clog_one_more (x : ℕ) : Nat.clog 2 (x+1)≤Nat.clog 2 x+1 := by
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  rw [pow_succ]
  have:=Nat.le_pow_clog (by decide : 1<2) x
  have:=Nat.two_pow_pos (Nat.clog 2 x)
  omega

theorem bundled_span (tp : 0<T) (bill : palette≤coeff*(seed+1)^8)
    (height : H≤(2*T)^s) (nodes : N≤(2*T)^s) (args : A≤(2*T)^s)
    («public» : Nat.clog 2 (q+1)≤(2*T)^s) (pgrain : Nat.clog 2 (p+1)≤(2*T)^s)
    (pointer : Nat.clog 2 (q+H+1)≤(2*T)^s) (fixed : Nat.clog 2 coeff≤(2*T)^s)
    (seedWidth : Nat.clog 2 (seed+1)≤(2*T)^s) (birth : arity≤(2*T)^s)
    (parts : slices≤(2*T)^s) (step : Nat.clog 2 (drift+2)≤(2*T)^s) :
    span q (DescentBundleTagKeys.capacity palette arity slices p drift) H N A p+1≤(2*T)^(6*s+19) := by
  let d:=(2*T)^s;let big:=(2*T)^(2*s+5)
  have dp : 0<d:=by dsimp[d];positivity
  have cmp : d≤d*d:=Nat.le_mul_of_pos_right _ dp
  have lc (x : ℕ) : Nat.clog 2 (x+1)≤x := (Nat.clog_le_iff_le_pow (by decide)).mpr Nat.lt_two_pow_self
  have base:=palette_clog bill
  have words:=DescentBundleTagKeys.code_width palette (Nat.clog 2 palette) arity slices p drift (Nat.le_pow_clog (by decide) _)
  have hd : Nat.clog 2 (arity+1)≤d:=(lc _).trans birth
  have sl : Nat.clog 2 (slices+1)≤d:=(lc _).trans parts
  have product : arity*Nat.clog 2 (slices+1)≤d*d:=Nat.mul_le_mul birth sl
  have driftRoom : Nat.clog 2 (p+1)+2*Nat.clog 2 (drift+2)≤3*d:=by omega
  have books:=Nat.mul_le_mul parts driftRoom
  have enough : 0<2*T:=by omega
  have scale : 32*(d*d)≤big := by
    have b : 32≤(2*T)^5:=Nat.pow_le_pow_left (show 2≤2*T by omega) 5
    dsimp [big,d]
    rw [pow_add,Nat.mul_comm 2 s,pow_mul,pow_two]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right ((2*T)^s*((2*T)^s)) b
  have upper : d≤big:=by omega
  have tag : Nat.clog 2 (DescentBundleTagKeys.capacity palette arity slices p drift+1)≤big := by
    have more:=clog_one_more (DescentBundleTagKeys.capacity palette arity slices p drift)
    unfold DescentBundleTagKeys.width at words
    rw [show d*(3*d)=3*(d*d) by ring] at books
    omega
  have full:=span_polynomial (s:=2*s+5) tp (nodes.trans upper) (height.trans upper) (args.trans upper)
    («public».trans upper) (pgrain.trans upper) tag (pointer.trans upper)
  simpa [show 3*(2*s+5)+4=6*s+19 by omega] using full

end
end Hierarchy.DescentTerminalVertexFields

end OAI
