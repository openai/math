import OAI.Optimization.LinearProgramming.RAM.CallableScopedRun
import OAI.Optimization.LinearProgramming.RAM.CallableOddBase
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Finite register bounds for the parity-packed normal LP entry. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialOrientation

open RAM RAM.Callable Polynomial

private theorem dimensions_index (m d i : ℕ) : (([m,d] : List ℕ)[i]?).getD 0 ≤ m+d := by
  cases value : ([m,d] : List ℕ)[i]? with
  | none => exact Nat.zero_le _
  | some x =>
    have member := List.mem_of_getElem? value
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> simp

/-- The empty even bank starts with zero addresses. The odd bank carries only the
translated row count, column count and zero of the standard LP input. -/
theorem physical_start_index {K : Type*} [Zero K] (m d : ℕ) (xs : List K) (i : ℕ) :
    (Odd.memory (start [] ([] : List K)).memory (start [m,d] xs).memory).index i ≤ 2*(m+d)+1 := by
  by_cases even : i%2 = 0
  · rw [show i = 2*(i/2) by omega,Odd.index_even]
    change 2*(([] : List ℕ)[i/2]?).getD 0 ≤ 2*(m+d)+1
    simp
  · rw [show i = Odd.slot (i/2) by unfold Odd.slot; omega,Odd.index_slot]
    change 2*(([m,d] : List ℕ)[i/2]?).getD 0+1 ≤ 2*(m+d)+1
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (dimensions_index m d (i/2))) 1

/-- A single polynomial bounds the final logical addresses of any fixed-access
fragment started with the public LP address registers. -/
noncomputable def addressPolynomial (f : Fragment) (time : Polynomial ℕ) : Polynomial ℕ :=
  C f.localBudget + (2*X+1) + time

theorem addressPolynomial_eval (f : Fragment) (time : Polynomial ℕ) (u : ℕ) :
    (addressPolynomial f time).eval u = f.localBudget+(2*u+1)+time.eval u := by
  simp [addressPolynomial]

theorem logical_address_bound {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : Fragment) [f.FixedAccess] (time : Polynomial ℕ) (m d : ℕ)
    (xs : List K) {P : K → Prop} {front back : Memory K} {k : ℕ}
    (elapsed : k ≤ time.eval (m+d))
    (run : f.Run P (Odd.memory (start [] ([] : List K)).memory (start [m,d] xs).memory) k (Odd.memory front back))
    (j : ℕ) : back.index j ≤ (addressPolynomial f time).eval (m+d) := by
  let B := f.localBudget+(2*(m+d)+1)
  have localCode : f.Scoped B := (Fragment.scoped_localBudget f).mono (Nat.le_add_right ..)
  have initial (i : ℕ) : (Odd.memory (start [] ([] : List K)).memory (start [m,d] xs).memory).index i ≤ B := by
    exact (physical_start_index m d xs i).trans (Nat.le_add_left ..)
  have physical := run.final_index_bound localCode initial (Odd.slot j)
  rw [Odd.index_slot] at physical
  unfold Odd.slot at physical
  dsimp only [B] at physical
  rw [addressPolynomial_eval]
  omega

end InitialOrientation
end Recovery
end LinearProgramming
end Optimization
end OAI
