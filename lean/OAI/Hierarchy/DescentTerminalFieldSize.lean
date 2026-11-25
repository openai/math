import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI
/-! # The full bit width of the literal terminal vertex fields -/
namespace Hierarchy.DescentTerminalLeafDigits
abbrev Coord (V H N A : ℕ) :=
  Unit ⊕ (Fin V ⊕ (Fin V ⊕ ((Fin V×Fin H) ⊕ ((Fin V×Fin N) ⊕ ((Fin V×Fin N) ⊕ (Fin V×Fin N×Fin A))))))
def radix (q t V H N A w : ℕ) : Coord V H N A→ℕ :=
  Sum.elim (fun _=>V+1) (Sum.elim (fun _=>H+1) (Sum.elim (fun _=>N+1)
    (Sum.elim (fun _=>w+1) (Sum.elim (fun _=>t+1) (Sum.elim (fun _=>A+1) (fun _=>q+H+1))))))

end Hierarchy.DescentTerminalLeafDigits

namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalLeafDigits
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w : ℕ}
abbrev Key (H N A : ℕ) := Unit⊕Coord 1 H N A
def bound (q t H N A w : ℕ) : Key H N A→ℕ := Sum.elim (fun _=>q+1) (radix q t 1 H N A w)
def bits (q t H N A w : ℕ) (k : Key H N A) := Nat.clog 2 (bound q t H N A w k)
def span (q t H N A w : ℕ) := ∑k : Key H N A,bits q t H N A w k
/-- This is exactly the sum of the bit widths of the real field coordinates. -/
theorem size : span q t H N A w=Nat.clog 2 (q+1)+1+
    (Nat.clog 2 (H+1)+Nat.clog 2 (N+1)+H*Nat.clog 2 (w+1)+
    N*Nat.clog 2 (t+1)+N*Nat.clog 2 (A+1)+N*A*Nat.clog 2 (q+H+1)) := by
  simp [span,bits,bound,radix,Fintype.sum_sum_type,Finset.sum_const]
 ; ring

end
end Hierarchy.DescentTerminalVertexFields

namespace Hierarchy.DescentTerminalVertexFields
noncomputable section
variable {q tags H N A w T s : ℕ}

/-- Counts and arities refer to one real vertex; public inputs, arities,
private labels and the literal dictionary are measured in bits. -/
theorem span_polynomial (positive : 0<T) (nodes : N≤(2*T)^s) (hidden : H≤(2*T)^s) (slots : A≤(2*T)^s)
    (publicWidth : Nat.clog 2 (q+1)≤(2*T)^s) (width : Nat.clog 2 (w+1)≤(2*T)^s)
    (role : Nat.clog 2 (tags+1)≤(2*T)^s) (pointer : Nat.clog 2 (q+H+1)≤(2*T)^s) :
    span q tags H N A w+1≤(2*T)^(3*s+4) := by
  let d:=(2*T)^s
  have one : 1≤d := Nat.pow_pos (Nat.mul_pos (by decide) positive)
  have two : d≤d*d:=Nat.le_mul_of_pos_left _ one
  have three : d*d≤d*d*d:=Nat.le_mul_of_pos_right _ one
  have lg (x : ℕ) : Nat.clog 2 (x+1)≤x := (Nat.clog_le_iff_le_pow (by decide)).mpr Nat.lt_two_pow_self
  have hc:=(lg H).trans hidden;have nc:=(lg N).trans nodes;have ac:=(lg A).trans slots
  have bill : span q tags H N A w+1≤d+1+(d+d+d*d+d*d+d*d+d*d*d)+1 := by
    rw [size]
    gcongr
  have d1 := two.trans three
  have low : 16≤(2*T)^4:=Nat.pow_le_pow_left (show 2≤2*T by omega) 4
  have const : 10≤(2*T)^4:=by omega
  calc
    _ ≤ 10*(d*d*d) := by omega
    _ ≤ (2*T)^4*(d*d*d) := Nat.mul_le_mul_right _ const
    _ = _ := by dsimp [d];rw [pow_add,Nat.mul_comm 3 s,pow_mul];ring

end
end Hierarchy.DescentTerminalVertexFields

end OAI
