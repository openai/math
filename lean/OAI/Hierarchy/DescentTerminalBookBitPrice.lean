import OAI.Hierarchy.DescentTerminalBookRadices
import OAI.Hierarchy.DescentTerminalRouteDimensions
import Mathlib.Tactic

namespace OAI
/-! # Complete terminal book, numeric lookup weights and mixed request keys -/
namespace Hierarchy.DescentTerminalLocalPortBook.Book
open scoped BigOperators
noncomputable section

theorem capacity_pos (G V M A a : ℕ) (i : Fin 6) : 0 < capacities G V M A a i := by
  fin_cases i <;> simp [capacities] <;> positivity

theorem stride_pos (G V M A a : ℕ) (i : Fin 6) : 0 < strides G V M A a i := by
  have p:=capacity_pos G V M A a
  have p45:=Nat.mul_pos (p 4) (p 5)
  have p345:=Nat.mul_pos (p 3) p45
  have p2345:=Nat.mul_pos (p 2) p345
  fin_cases i
  · exact Nat.mul_pos (p 1) p2345
  · exact p2345
  · exact p345
  · exact p45
  · exact p 5
  · exact Nat.zero_lt_one

/-- Each literal field-weight table has its actual cardinality as domain,
and its largest output digit times its own physical stride fits the book. -/
theorem capacity_stride (G V M A a : ℕ) (i : Fin 6) :
    capacities G V M A a i*strides G V M A a i ≤ Bytes G V M A a := by
  let n:=capacities G V M A a
  have p:=capacity_pos G V M A a
  have h₁:=Nat.le_mul_of_pos_left (n 1*(n 2*(n 3*(n 4*n 5)))) (p 0)
  have h₂:=Nat.le_mul_of_pos_left (n 2*(n 3*(n 4*n 5))) (p 1)
  have h₃:=Nat.le_mul_of_pos_left (n 3*(n 4*n 5)) (p 2)
  have h₄:=Nat.le_mul_of_pos_left (n 4*n 5) (p 3)
  have h₅:=Nat.le_mul_of_pos_left (n 5) (p 4)
  fin_cases i
  · exact le_rfl
  · exact h₁
  · exact h₂.trans h₁
  · exact h₃.trans (h₂.trans h₁)
  · exact h₄.trans (h₃.trans (h₂.trans h₁))
  · change n 5*1≤_
    rw [Nat.mul_one]
    exact h₅.trans (h₄.trans (h₃.trans (h₂.trans h₁)))

theorem capacity_fit (G V M A a : ℕ) (i : Fin 6) :
    capacities G V M A a i ≤ Bytes G V M A a :=
  (Nat.le_mul_of_pos_right _ (stride_pos G V M A a i)).trans (capacity_stride G V M A a i)

theorem weight_fit {G V M A a : ℕ} (i : Fin 6) (v : Fin (capacities G V M A a i)) :
    v.val*strides G V M A a i < Bytes G V M A a :=
  (Nat.mul_lt_mul_of_pos_right v.isLt (stride_pos G V M A a i)).trans_le (capacity_stride G V M A a i)

abbrev tokenBits (M : ℕ) := nameBits 4 M

/-- The book uses an actual four-port directory, a length-`A` formal
argument array for each of `V` nodes and one local token per incidence. -/
theorem bytes_envelope (V A n : ℕ) (v : V≤n) (m : V*A≤n) (a : A≤n) (pos : 0<n) :
    Bytes 4 V (V*A) A (tokenBits (V*A)) ≤ 2^(60*(n*n)) := by
  let M:=V*A
  let bits:=tokenBits M
  have bitsBound : bits≤5*n := by
    apply Nat.clog_le_of_le_pow
    exact (show 4*M+1≤5*n by dsimp only [M];omega).trans (Nat.lt_two_pow_self.le)
  have bit0 : 4+1≤2^3 := by decide
  have bit1 : V+1≤2^(n+1) := (Nat.succ_le_succ v).trans (Nat.lt_two_pow_self.le)
  have bit2 : M+1≤2^(n+1) := (Nat.succ_le_succ m).trans (Nat.lt_two_pow_self.le)
  have bit3 : A+1≤2^(n+1) := (Nat.succ_le_succ a).trans (Nat.lt_two_pow_self.le)
  have charged : (n+1)*V ≤ (n+1)*n := Nat.mul_le_mul_left _ v
  have tokenCost : bits*M≤5*n*n := Nat.mul_le_mul bitsBound m
  have sq : n≤n*n:=Nat.le_mul_of_pos_right _ pos
  calc
    _ ≤ 2^3*(2^(n+1)*((2^(n+1))^4*((2^(n+1))^V*(((2^bits)^M)^4*((2^bits)^A)^V)))) :=
      Nat.mul_le_mul bit0 (Nat.mul_le_mul bit1 (Nat.mul_le_mul (Nat.pow_le_pow_left bit2 _)
        (Nat.mul_le_mul (Nat.pow_le_pow_left bit3 _) le_rfl)))
    _ = 2^(3+(n+1)+4*(n+1)+(n+1)*V+4*(bits*M)+bits*M) := by
      simp only [←pow_mul,←pow_add]
      congr 1
      dsimp only [M]
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)

end
end Hierarchy.DescentTerminalLocalPortBook.Book

end OAI
