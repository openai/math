import OAI.Optimization.LinearProgramming.RAM.RAMDatum
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.GCongr

/-! Polynomial bounds for the values and evaluation costs of address and data terms. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Tape

open Polynomial

namespace AddressTerm
variable {n : Nat}

noncomputable def boundValue : AddressTerm n → Polynomial Nat
  | .reg _ => X
  | .val k => C k
  | .binary .plus l r => boundValue l + boundValue r
  | .binary .minus l _ => boundValue l
  | .binary .times l r => boundValue l * boundValue r

noncomputable def boundCost : AddressTerm n → Polynomial Nat
  | .reg _ | .val _ => 1
  | .binary o l r => boundCost l + (boundCost r + match o with
    | .plus | .minus => 2+4*boundValue r
    | .times => 4+(5+4*boundValue l)*boundValue r)

theorem value_le (e : AddressTerm n) (env : Fin n → Nat) (B : Nat) (h : ∀ i, env i ≤ B) :
    e.value env ≤ e.boundValue.eval B := by
  induction e with
  | val k => simp [value,boundValue]
  | reg i => simpa [value,boundValue] using h i
  | binary o l r hl hr =>
    cases o <;> simp only [value,boundValue,AddressOp.value,eval_add,eval_mul]
    · exact Nat.add_le_add hl hr
    · exact (Nat.sub_le _ _).trans hl
    · exact Nat.mul_le_mul hl hr

theorem cost_le (e : AddressTerm n) (env : Fin n → Nat) (B : Nat) (h : ∀ i, env i ≤ B) :
    e.cost env ≤ e.boundCost.eval B := by
  induction e with
  | val k => simp [cost,boundCost]
  | reg i => simp [cost,boundCost]
  | binary o l r hl hr =>
    have hv := value_le l env B h
    have hv' := value_le r env B h
    cases o <;> simp [cost,boundCost,AddressOp.cost] <;> gcongr

end AddressTerm

namespace DatumTerm
variable {n : Nat}

noncomputable def boundCost : DatumTerm n → Polynomial Nat
  | .zero | .negOne => 1
  | .word e _ => 1+(e.boundCost+(2+4*e.boundValue))+2
  | .lt l r yes no => l.boundCost+(r.boundCost+(2+(boundCost yes + boundCost no)))

theorem cost_le (e : DatumTerm n) (env : Fin n → Nat) (src : Fin n) {B : Nat} (h : ∀ i, env i ≤ B) :
    e.cost env src ≤ e.boundCost.eval B := by
  induction e with
  | zero | negOne => simp [boundCost,cost]
  | word e neg =>
    change 1+(e.cost env+(2+4*e.value env))+2 ≤ _
    simp [boundCost]
    gcongr
    · exact e.cost_le env B h
    · exact e.value_le env B h
  | lt l r yes no hy hn =>
    simp [cost,boundCost]
    have hm : max (yes.cost env src) (no.cost env src) ≤ yes.boundCost.eval B+no.boundCost.eval B :=
      max_le (by omega) (by omega)
    gcongr
    · exact l.cost_le env B h
    · exact r.cost_le env B h

end DatumTerm
end Tape
end RAM
end LinearProgramming
end Optimization
end OAI
