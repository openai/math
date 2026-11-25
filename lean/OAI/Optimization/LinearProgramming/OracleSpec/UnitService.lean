import OAI.Optimization.LinearProgramming.OracleSpec.IndexOrder
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! A uniform implementation of the online minor-log interface on unit-magnitude inputs,
including the zero-dimensional pair of matrices. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace MinorLog

/-- Emit the canonical reduced bits of `0/1`, including its sign bit. -/
def zeroAnswerProgram : RAM.Program :=
  [.const 0 0, .addrConst 0 1, .addrConst 1 1, .addrConst 2 0,
   .addrConst 3 0, .addrConst 4 1, .halt 0]

private theorem zeroAnswer_run {s : RAM.State ℚ} (hp : s.pc = 0) (ho : s.output = none)
    {clock H : ℕ} (htime : 7 ≤ clock) (hH : 3 ≤ H) (hs : RAM.scalarBound H s) :
    ∃ t, call zeroAnswerProgram clock H s t ∧ emits t (some 0) ∧ RAM.scalarBound H t := by
  have hlog : (1 : ℕ).log2 = 0 := rfl
  let a := s.putData 0 0
  let b := a.putIndex 0 1
  let c := b.putIndex 1 1
  let d := c.putIndex 2 0
  let e := d.putIndex 3 0
  let g := e.putIndex 4 1
  let t := { g with output := some 0 }
  let trace : Fin 8 → RAM.State ℚ := ![s, a, b, c, d, e, g, t]
  have safe : ∀ i, RAM.scalarBound H (trace i) := by
    intro i j
    have hb : (trace i).data = s.data ∨ (trace i).data = Function.update s.data 0 0 := by
      fin_cases i <;> simp [trace, a, b, c, d, e, g, t, RAM.State.putData, RAM.State.putIndex]
    rcases hb with he | he
    · rw [he]; exact hs j
    · rw [he]; by_cases hj : j = 0
      · simpa [hj, RAM.ratBits, hlog] using hH
      · simpa [Function.update_of_ne hj] using hs j
  refine ⟨t, ⟨7, htime, trace, ⟨rfl, ?_⟩, rfl, safe⟩, ?_, safe (Fin.last 7)⟩
  · intro i
    fin_cases i <;> simp [trace, zeroAnswerProgram, RAM.step, RAM.execInstr, RAM.State.putData,
      RAM.State.putIndex, a, b, c, d, e, g, t, hp, ho]
  · change t.output = some 0 ∧ explicitValue t 0
    refine ⟨rfl, ?_⟩
    simp [explicitValue, width, t, g, e, d, c, b, a, RAM.State.putIndex, RAM.State.putData,
      Function.update, hlog]

private theorem word_length_le {r s n : ℕ} (u : RawIndex r s n) : (words u).length ≤ 2 + 2*n := by
  cases u with
  | inl u => rw [words, squareWords_length]; have := u.order.isLt; omega
  | inr u => rw [words, squareWords_length]; have := u.order.isLt; omega

private theorem zeroAnswer_processes {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ}
    {E : Matrix (Fin s) (Fin n) ℚ} (us : List (Index D E)) {H : ℕ} (hH : 3 ≤ H)
    (st : RAM.State ℚ) (hs : RAM.scalarBound H st) :
    Processes (fun u : Index D E ↦ words u.val) zeroAnswerProgram (16*(n+1)) H (16*(n+1))
      st us (us.map (fun u ↦ (u,some 0))) := by
  induction us generalizing st with
  | nil => exact .nil _
  | cons u us ih =>
    have hw := word_length_le u.val
    obtain ⟨t, ht, emit, safe⟩ := zeroAnswer_run (s := resume st (words u.val)) rfl rfl
      (clock := 16*(n+1) - (words u.val).length) (by omega) hH hs
    refine .cons ht (by omega) emit (fun q he ↦ ?_) (ih t safe)
    cases he; change 3 ≤ 16*(n+1); omega

private theorem start_height (dims : List ℕ) (input : List ℚ) :
    RAM.scalarBound (16 * ((input.map RAM.ratBits).sum+1)) (RAM.start dims input) := by
  intro j
  change RAM.ratBits (input[j]?.getD 0) ≤ _
  cases hx : input[j]? with
  | none => simp only [Option.getD_none]; change 3 ≤ _; omega
  | some x =>
    have h := List.le_sum_of_mem (List.mem_map_of_mem (f := RAM.ratBits) (List.mem_of_getElem? hx))
    change RAM.ratBits x ≤ _; omega

private theorem initZero_run (dims : List ℕ) (input : List ℚ) (clock : ℕ) (hclock : 1 ≤ clock) :
    let H := 16 * ((input.map RAM.ratBits).sum+1)
    ∃ ready : RAM.State ℚ, call [.halt 0] clock H (RAM.start dims input) ready ∧
      ready.output = some 0 ∧ RAM.scalarBound H ready := by
  let s := RAM.start dims input
  let ready := {s with output := some 0}
  let tr : Fin 2 → RAM.State ℚ := ![s, ready]
  have safe := start_height dims input
  refine ⟨ready, ⟨1, hclock, tr, ⟨rfl, ?_⟩, rfl, ?_⟩, rfl, safe⟩
  · intro i; fin_cases i; rfl
  · intro i; fin_cases i <;> exact safe

/-- Every prefix of the constant-zero stream extends to the same zero assignment. -/
theorem zeroHistory_extension {ι : Type} (n : ℕ) {logs : ι → ℝ} (hl : ∀ i, logs i = 0)
    (us : List ι) (j exponent : ℕ) :
    extension n exponent logs ((us.map (fun u ↦ (u,some 0))).take j) := by
  refine ⟨fun _ ↦ 0, ?_, fun i ↦ by simp, ?_⟩
  · have h (xs : List ι) : agreesSinceRestart (fun _ ↦ 0) ((xs.map (fun u ↦ (u,some 0))).reverse) := by
      induction xs using List.reverseRecOn with
      | nil => exact True.intro
      | append_singleton x xs ih => simpa [agreesSinceRestart] using ih
    simpa using h (us.take j)
  · intro a _
    simp [hl]

/-- All nonzero minors of unit magnitude have logarithm zero, even on the empty request prefix.
This family satisfies the full external RAM, register-height and response-stream contracts. -/
theorem unitMinor_online_compression {r s n : ℕ} (D : Matrix (Fin r) (Fin n) ℚ)
    (E : Matrix (Fin s) (Fin n) ℚ) (hu : ∀ u : Index D E, |minor D E u.val| = 1) :
    let input := entries D ++ entries E
    let clock := 16*(n+1)
    let H := 16*((input.map RAM.ratBits).sum+1)
    ∃ ready : RAM.State ℚ, call [.halt 0] clock H (RAM.start [r,s,n] input) ready ∧
      ready.output = some 0 ∧ ∀ requests : List (Index D E), ∃ replies,
        Processes (fun u : Index D E ↦ words u.val) zeroAnswerProgram clock H clock ready requests replies ∧
        restartCount replies = 0 ∧ ∀ j ≤ replies.length, extension n clock (logarithm D E) (replies.take j) := by
  let input := entries D ++ entries E
  obtain ⟨ready, hi, hr, hs⟩ := initZero_run [r,s,n] input (16*(n+1)) (by omega)
  refine ⟨ready, hi, hr, fun req ↦ ?_⟩
  refine ⟨req.map (fun u ↦ (u,some 0)), zeroAnswer_processes req (by omega) ready hs, ?_, ?_⟩
  · simp [restartCount]
  · intro j _
    apply zeroHistory_extension
    intro i
    have hi' : |(minor D E i.val : ℝ)| = 1 := by exact_mod_cast hu i
    simp [logarithm, hi']

/-- In zero columns every square minor of either matrix is the empty determinant. -/
theorem zeroColumns_unitMinor {r s : ℕ} (D : Matrix (Fin r) (Fin 0) ℚ)
    (E : Matrix (Fin s) (Fin 0) ℚ) (u : Index D E) : |minor D E u.val| = 1 := by
  rcases u with ⟨u, _⟩
  cases u with
  | inl u => rcases u with ⟨k, rows, cols, hr, hc⟩; fin_cases k; simp [minor, Matrix.det_isEmpty]
  | inr u => rcases u with ⟨k, rows, cols, hr, hc⟩; fin_cases k; simp [minor, Matrix.det_isEmpty]

end MinorLog
end OracleSpec
end LinearProgramming
end Optimization
end OAI
