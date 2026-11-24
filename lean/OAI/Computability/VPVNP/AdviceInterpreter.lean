import OAI.Computability.VPVNP.AdviceBitLookup
import OAI.Computability.VPVNP.AdviceCircuitProgram
import OAI.Computability.VPVNP.StructuredStackLoop

/-!
# A fixed bit-stack interpreter for Boolean circuit advice

The stream contains a gate tag followed by one or two unary operand addresses.
Each lookup preserves the valuation stack. The gate body removes its operand
bits from scratch and prepends its result to the valuation stack. The control
and the four stacks are fixed independently of the circuit, input and gate count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.AdviceInterpreter

open AdviceCircuit
open AdviceBitLookup (Port store)

private def reject : Routine Port Unit := Routine.halt false
private def put (v : Bool) : Routine Port Unit := Routine.push .values v

private def unaryBody := Routine.popCase .result reject (put true) (put false)
private def second (v : Bool) := Routine.popCase .result reject (put false) (put v)
private def binaryBody := Routine.popCase .result reject (second false) (second true)

private def unaryGate : FiniteRoutine Port :=
  AdviceBitLookup.routine.followedBy (.ofRoutine unaryBody)

private def binaryGate : FiniteRoutine Port :=
  (AdviceBitLookup.routine.followedBy AdviceBitLookup.routine).followedBy (.ofRoutine binaryBody)

/-- Executable instruction loop. An exhausted advice stream returns to the caller. -/
def routine : FiniteRoutine Port :=
  .ofRoutine (Routine.popLoop .stream (fun _ ↦ true) unaryGate.body binaryGate.body)

private theorem update_stream (a v s r t : List Bool) :
    Function.update (store a v s r) .stream t = store t v s r := by funext i; cases i <;> simp [store]

private theorem update_values (a v s r t : List Bool) :
    Function.update (store a v s r) .values t = store a t s r := by funext i; cases i <;> simp [store]

private theorem update_result (a v s r t : List Bool) :
    Function.update (store a v s r) .result t = store a v s t := by funext i; cases i <;> simp [store]

private theorem put_runs (b : Bool) (s v : List Bool) :
    (put b).Runs 1 (store s v [] []) (store s (b :: v) [] []) := by
  simpa only [put, update_values, store] using Routine.runs_push Port.values b (store s v [] [])

private theorem unary_runs (b : Bool) (s v : List Bool) :
    unaryBody.Runs 2 (store s v [] [b]) (store s ((!b) :: v) [] []) := by
  cases b
  · apply Routine.runs_popCase_false (s := store s v [] [false]) (t := 1) .result reject
      (put true) (put false) rfl
    rw [update_result]; exact put_runs _ _ _
  · apply Routine.runs_popCase_true (s := store s v [] [true]) (t := 1) .result reject
      (put true) (put false) rfl
    rw [update_result]; exact put_runs _ _ _

private theorem second_runs (a b : Bool) (s v : List Bool) :
    (second b).Runs 2 (store s v [] [a]) (store s ((a && b) :: v) [] []) := by
  cases a
  · apply Routine.runs_popCase_false (s := store s v [] [false]) (t := 1) .result reject
      (put false) (put b) rfl
    rw [update_result]; exact put_runs _ _ _
  · apply Routine.runs_popCase_true (s := store s v [] [true]) (t := 1) .result reject
      (put false) (put b) rfl
    rw [update_result]; exact put_runs _ _ _

private theorem binary_runs (a b : Bool) (s v : List Bool) :
    binaryBody.Runs 3 (store s v [] [b,a]) (store s ((a && b) :: v) [] []) := by
  cases b
  · apply Routine.runs_popCase_false (s := store s v [] [false, a]) (t := 2) .result reject
      (second false) (second true) rfl
    rw [update_result]; exact second_runs _ _ _ _
  · apply Routine.runs_popCase_true (s := store s v [] [true, a]) (t := 2) .result reject
      (second false) (second true) rfl
    rw [update_result]; exact second_runs _ _ _ _

private theorem unaryGate_runs (a : ℕ) (s v : List Bool) (ha : a < v.length) :
    unaryGate.Runs (5*a+7) (store (unary a ++ s) v [] []) (store s ((!v[a]) :: v) [] []) := by
  simpa only [unaryGate, unary, List.append_assoc, List.singleton_append, Nat.add_assoc] using
    FiniteRoutine.Runs.followedBy (AdviceBitLookup.routine_runs v s [] a ha)
      (show (FiniteRoutine.ofRoutine unaryBody).Runs 2 _ _ from unary_runs v[a] s v)

private theorem binaryGate_runs (a b : ℕ) (s v : List Bool) (ha : a < v.length) (hb : b < v.length) :
    binaryGate.Runs (5*a+5+(5*b+5)+3) (store (unary a ++ unary b ++ s) v [] [])
      (store s ((v[a] && v[b]) :: v) [] []) := by
  simpa only [binaryGate, unary, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
    FiniteRoutine.Runs.followedBy
      (FiniteRoutine.Runs.followedBy (AdviceBitLookup.routine_runs v (unary b ++ s) [] a ha)
        (by simpa only [unary, List.append_assoc, List.singleton_append] using
          AdviceBitLookup.routine_runs v s [v[a]] b hb))
      (show (FiniteRoutine.ofRoutine binaryBody).Runs 3 _ _ from binary_runs v[a] v[b] s v)

/-- A successful abstract execution is implemented by at most sixteen stack
instructions per advice bit, including the final end-of-stream test. -/
theorem routine_runs (p : List Instruction) (v u : List Bool) (hu : run p v = some u) :
    ∃ t ≤ 16 * ((encode p).length + 1), routine.Runs t (store (encode p) v [] []) (store [] u [] []) := by
  induction p generalizing v with
  | nil =>
    obtain rfl : v = u := Option.some.inj hu
    refine ⟨1, by simp [encode], ?_⟩
    change (Routine.popLoop Port.stream (fun _ ↦ true) unaryGate.body binaryGate.body).Runs
      1 (store [] v [] []) (store [] v [] [])
    exact Routine.Runs.popLoop_empty (s := store [] v [] []) Port.stream (fun _ ↦ true)
      unaryGate.body binaryGate.body rfl
  | cons i p ih =>
    cases i with
    | not a =>
      by_cases ha : a < v.length
      · have val : (Instruction.not a).value v = some (!v[a]) := by
          simp [Instruction.value, List.getElem?_eq_getElem ha]
        rw [run_cons val] at hu
        obtain ⟨t, ht, hh⟩ := ih _ hu
        refine ⟨1+(5*a+7)+t, ?_, ?_⟩
        · simp only [encode, List.flatMap_cons, Instruction.encode, unary, List.length_append,
            List.length_cons, List.length_nil, List.length_replicate] at *
          omega
        · refine Routine.Runs.popLoop_false_continue (s := store (encode (.not a :: p)) v [] [])
            (tail := unary a ++ encode p) .stream (fun _ ↦ true) unaryGate.body binaryGate.body
            rfl rfl ?_ hh
          rw [update_stream]
          exact unaryGate_runs a (encode p) v ha
      · simp [run, Instruction.value, List.getElem?_eq_none_iff.mpr (by omega : v.length ≤ a)] at hu
    | and a b =>
      by_cases ha : a < v.length
      · by_cases hb : b < v.length
        · have val : (Instruction.and a b).value v = some (v[a] && v[b]) := by
            simp [Instruction.value, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]
          rw [run_cons val] at hu
          obtain ⟨t, ht, hh⟩ := ih _ hu
          refine ⟨1+(5*a+5+(5*b+5)+3)+t, ?_, ?_⟩
          · simp only [encode, List.flatMap_cons, Instruction.encode, unary, List.length_append,
              List.length_cons, List.length_nil, List.length_replicate] at *
            omega
          · refine Routine.Runs.popLoop_true_continue (s := store (encode (.and a b :: p)) v [] [])
              (tail := (unary a ++ unary b) ++ encode p) .stream (fun _ ↦ true) unaryGate.body binaryGate.body
              rfl rfl ?_ hh
            rw [update_stream]
            exact binaryGate_runs a b (encode p) v ha hb
        · simp [run, Instruction.value, List.getElem?_eq_getElem ha,
            List.getElem?_eq_none_iff.mpr (by omega : v.length ≤ b)] at hu
      · simp [run, Instruction.value, List.getElem?_eq_none_iff.mpr (by omega : v.length ≤ a)] at hu

end RAMTape.AdviceInterpreter

end VPVNP
end Computability
end OAI
