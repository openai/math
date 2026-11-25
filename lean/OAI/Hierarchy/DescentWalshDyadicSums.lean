import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI
/-! # Intermediate natural values in the zero-padded binary score reduction -/

namespace Hierarchy.DescentWalshDyadicSums
open scoped BigOperators
variable {H Q : ℕ}

def sample (x : Fin H→Fin Q→ℕ) (v : ℕ) (d : Fin Q) : ℕ :=
  if hv : v<H then x ⟨v,hv⟩ d else 0

def value (x : Fin H→Fin Q→ℕ) (t v : ℕ) (d : Fin Q) :=
  ∑j ∈ Finset.range (2^t),sample x (v*2^t+j) d

@[simp] theorem value_zero (x : Fin H→Fin Q→ℕ) (v : ℕ) (d : Fin Q) :
    value x 0 v d=sample x v d := by simp [value]

theorem value_succ (x : Fin H→Fin Q→ℕ) (t v : ℕ) (d : Fin Q) :
    value x (t+1) v d=value x t (2*v) d+value x t (2*v+1) d := by
  unfold value
  rw [show 2^(t+1)=2^t+2^t by rw [pow_succ];omega,Finset.sum_range_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;>
    apply congrArg (fun i => sample x i d) <;> ring

theorem value_finish (x : Fin H→Fin Q→ℕ) (d : Fin Q) :
    value x (Nat.clog 2 H) 0 d=∑i : Fin H,x i d := by
  have span : H≤2^Nat.clog 2 H := Nat.le_pow_clog (by decide) H
  unfold value
  simp only [Nat.zero_mul,Nat.zero_add]
  calc
    _ = ∑ j ∈ Finset.range H,sample x j d := by
      symm
      apply Finset.sum_subset (Finset.range_mono span)
      intro i hi off
      exact dite_eq_right (by simpa only [Finset.mem_range] using off)
    _ = ∑i : Fin H,sample x i.val d := (Fin.sum_univ_eq_sum_range (fun i=>sample x i d) H).symm
    _ = ∑i : Fin H,x i d := by simp [sample]

theorem value_lt (x : Fin H→Fin Q→ℕ) (b : ℕ) (h : ∀i d,x i d<2^b)
    (t v : ℕ) (d : Fin Q) : value x t v d<2^(b+t) := by
  induction t generalizing v with
  | zero=>
    rw [value_zero,Nat.add_zero]
    unfold sample
    split
    · exact h _ _
    · exact Nat.two_pow_pos _
  | succ t ih=>
    rw [value_succ, show b+(t+1)=(b+t)+1 by omega, pow_succ]
    have l:=ih (2*v)
    have r:=ih (2*v+1)
    omega

theorem absent (x : Fin H→Fin Q→ℕ) (t v : ℕ) (d : Fin Q) (away : H≤v*2^t) : value x t v d=0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact dite_eq_right (by omega)

end Hierarchy.DescentWalshDyadicSums

end OAI
