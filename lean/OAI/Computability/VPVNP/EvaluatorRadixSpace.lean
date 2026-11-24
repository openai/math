import OAI.Computability.VPVNP.EvaluatorRadixDivision

/-!
# Peak storage of the radix conversion

The exponent, divisor and requested number of rounds are all encoded on
stacks. Every instruction uses at most one additional bit. The exact
polynomial clock therefore gives a polynomial storage bound at every
intermediate point, including storage of the compact output digits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorRadixDivision

open RAMTape TapeWord

section Runs

variable {K Q : Type*} [DecidableEq K] {code : StackCode K Q}

private theorem step_unique {q r r' : Q} {s u u' : Stacks K} (h : StackStep code q s r u)
    (h' : StackStep code q s r' u') : r = r' ∧ u = u' := by
  cases h <;> cases h' <;> simp_all

theorem ticks_le_at_return {q r v : Q} {s out u : Stacks K} {m n : ℕ}
    (done : StackRuns code m q s r out) (halt : (code r).returns = true)
    (prefixRun : StackRuns code n q s v u) : n ≤ m := by
  induction done generalizing n with
  | nil =>
    cases prefixRun with
    | nil => exact le_rfl
    | cons h _ => cases h <;> simp_all
  | cons h _ ih =>
    cases prefixRun with
    | nil => exact Nat.zero_le _
    | cons h' tail =>
      obtain ⟨rfl, rfl⟩ := step_unique h h'
      exact Nat.succ_le_succ (ih halt tail)

private theorem step_length {q r : Q} {s u : Stacks K} (run : StackStep code q s r u) (k : K) :
    (u k).length ≤ (s k).length + 1 := by
  cases run with
  | goto => omega
  | push _ =>
    rename_i i b h
    by_cases hi : k = i <;> simp [Function.update, hi]
  | pop _ =>
    rename_i i f h
    by_cases hi : k = i <;> simp [Function.update, hi]
    omega

theorem run_length {q r : Q} {s u : Stacks K} {n : ℕ} (run : StackRuns code n q s r u)
    (k : K) : (u k).length ≤ (s k).length + n := by
  induction run with
  | nil => simp
  | cons h _ ih =>
    have hs := step_length h k
    omega

end Runs

/-- The bound holds for every intermediate configuration reached by the
routine. It depends on the divisor only through the length of its input
encoding. There are ten physical bit stacks. -/
theorem radixRoutine_space (rounds : ℕ) (x d acc : List Bool) (hd : 0 < value d)
    {n : ℕ} {q : Option radixRoutine.State} {u : Stacks Port}
    (run : StackRuns radixRoutine.body.standalone n (some radixRoutine.body.entry)
      (ready rounds x d acc) q u) :
    ∑ k, (u k).length ≤
      10 * (rounds + x.length + d.length + acc.length + radixTicks rounds x.length d.length) := by
  have hn := ticks_le_at_return (radixRoutine_runs rounds x d acc hd) (by rfl) run
  have bound (k : Port) :
      (u k).length ≤ rounds + x.length + d.length + acc.length + radixTicks rounds x.length d.length := by
    have hs := run_length run k
    have hi : (ready rounds x d acc k).length ≤ rounds + x.length + d.length + acc.length := by
      cases k with
      | rounds | digits => simp [ready, bank] <;> omega
      | word j => cases j <;> simp [ready, bank, DivisionStack.Data.stacks] <;> omega
    omega
  calc
    ∑ k, (u k).length ≤ ∑ _ : Port, (rounds + x.length + d.length + acc.length + radixTicks rounds x.length d.length) :=
      Finset.sum_le_sum (fun k _ => bound k)
    _ = _ := by simp [show Fintype.card Port = 10 by decide]

end EvaluatorRadixDivision

end VPVNP
end Computability
end OAI
