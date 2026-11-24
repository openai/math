import OAI.Computability.BinPacking.CookLevin.ConfigIndex
import OAI.Computability.VPVNP.UniversalMachine

/-!
# Literal substring tests for the universal machine

The table interpreter tests an encoded field or row at a specified position
in its input. Every bit is checked by an input literal. An empty word can match
at the end of the input, and any test that extends past the input fails.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace VerifierMachineDecode

open UniversalMachine
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

private def literal {n : ℕ} (i : Fin n) (b : Bool) : Expr (Fin n) :=
  if b then .input i else .not (.input i)

private theorem eval_literal {n : ℕ} (x : Fin n → Bool) (i : Fin n) (b : Bool) :
    (literal i b).eval x = true ↔ x i = b := by
  cases b <;> simp [literal, Expr.eval]

/-- Conjunction of the literals of `word`, starting at zero-based position `j`. -/
def matchAt (n j : ℕ) : Word → Expr (Fin n)
  | [] => .const (decide (j ≤ n))
  | b :: word =>
    if hj : j < n then .and (literal ⟨j, hj⟩ b) (matchAt n (j + 1) word)
    else .const false

theorem eval_matchAt_drop {n : ℕ} (x : Fin n → Bool) (j : ℕ) (word : Word) :
    (matchAt n j word).eval x = true ↔ j ≤ n ∧ ∃ t, (List.ofFn x).drop j = word ++ t := by
  induction word generalizing j with
  | nil => simp [matchAt, Expr.eval]
  | cons b word ih =>
    by_cases hj : j < n
    · have hj' : j < (List.ofFn x).length := by simpa using hj
      rw [List.drop_eq_getElem_cons hj']
      simp [matchAt, Expr.eval, hj, eval_literal, ih, hj.le, Nat.succ_le_of_lt hj]
    · have hd : (List.ofFn x).drop j = [] :=
        List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_gt hj)
      simp [matchAt, hj, Expr.eval, hd]

/-- The input contains `word` after a prefix of length `j`. -/
def MatchAt (input : Word) (j : ℕ) (word : Word) : Prop :=
  ∃ s t, input = s ++ word ++ t ∧ s.length = j

theorem matchAt_iff_drop (input : Word) (j : ℕ) (word : Word) :
    MatchAt input j word ↔ j ≤ input.length ∧ ∃ t, input.drop j = word ++ t := by
  constructor
  · rintro ⟨s, t, rfl, rfl⟩
    exact ⟨by simp, t, by simp [List.append_assoc]⟩
  · rintro ⟨hj, t, ht⟩
    exact ⟨input.take j, t, by rw [List.append_assoc, ← ht, List.take_append_drop],
      by simp [hj]⟩

theorem MatchAt.end_le {input word : Word} {j : ℕ} (h : MatchAt input j word) :
    j + word.length ≤ input.length := by
  obtain ⟨s, t, rfl, rfl⟩ := h
  simp

/-- Matching two adjacent words is equivalent to matching their concatenation. -/
theorem matchAt_append_iff (input : Word) (j : ℕ) (a b : Word) :
    MatchAt input j (a ++ b) ↔ MatchAt input j a ∧ MatchAt input (j + a.length) b := by
  constructor
  · rintro ⟨s, t, rfl, rfl⟩
    exact ⟨⟨s, b ++ t, by simp [List.append_assoc], rfl⟩,
      ⟨s ++ a, t, by simp [List.append_assoc], by simp⟩⟩
  · rintro ⟨⟨s, rest, rfl, rfl⟩, hb⟩
    obtain ⟨_, t, ht⟩ := (matchAt_iff_drop _ _ _).mp hb
    have hrest : rest = b ++ t := by
      rw [← List.length_append, List.drop_left] at ht
      exact ht
    exact ⟨s, t, by simp [hrest, List.append_assoc], rfl⟩

/-- Acceptance is exactly occurrence of the specified word after a prefix of length `j`. -/
theorem eval_matchAt {n : ℕ} (x : Fin n → Bool) (j : ℕ) (word : Word) :
    (matchAt n j word).eval x = true ↔ MatchAt (List.ofFn x) j word := by
  rw [eval_matchAt_drop, matchAt_iff_drop, List.length_ofFn]

/-- Each bit contributes at most an input node, a negation, and a conjunction. -/
theorem size_matchAt (n j : ℕ) (word : Word) :
    (matchAt n j word).size ≤ 3 * word.length + 1 := by
  induction word generalizing j with
  | nil => simp [matchAt, Expr.size]
  | cons b word ih =>
    specialize ih (j + 1)
    by_cases hj : j < n
    · cases b <;> simp [matchAt, hj, literal, Expr.size] <;> omega
    · simp [matchAt, hj, Expr.size]

end VerifierMachineDecode

end VPVNP
end Computability
end OAI
