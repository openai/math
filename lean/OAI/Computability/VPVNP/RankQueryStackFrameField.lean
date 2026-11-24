import OAI.Computability.VPVNP.EvaluatorInputBank

/-!
# Saving and restoring one variable-length Schur frame field

Saving empties the live register and prepends the tagged field to its history
stack. Popping uses the evaluator's existing self-delimiting field reader.
Both routines use a fixed control independent of the register width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.FrameStore

open RAMTape Evaluator.InputBank

/-- Control phases for moving a field's bits into its delimited history encoding. -/
inductive WritePhase where
  | start | scan | payload (b : Bool) | tag
  deriving DecidableEq, Fintype

private abbrev pair (value history : List Bool) : Stacks (Option Unit) :=
  frame history (fun _ => value)

private def writer : Routine (Option Unit) WritePhase where
  entry := .start
  code
    | .start => .push none false (some .scan)
    | .scan => .pop (some ()) fun b => b.map .payload
    | .payload b => .push none b (some .tag)
    | .tag => .push none true (some .scan)

private theorem update_value (s h x : List Bool) :
    Function.update (pair s h) (some ()) x = pair x h := by
  funext k; cases k with
  | none => rfl
  | some v => cases v; rfl

private theorem update_history (s h x : List Bool) :
    Function.update (pair s h) none x = pair s x := by
  funext k; cases k with
  | none => rfl
  | some v => cases v; rfl

private theorem append_bit (pre : List Bool) (b : Bool) :
    fieldBits (pre ++ [b]) = true :: b :: fieldBits pre := by
  simp only [fieldBits, List.reverse_append, List.reverse_singleton, List.singleton_append]
  rfl

private theorem scan_runs (rest pre h : List Bool) :
    StackRuns writer.standalone (3*rest.length + 1) (some .scan)
      (pair rest (fieldBits pre ++ h)) none (pair [] (fieldBits (pre ++ rest) ++ h)) := by
  induction rest generalizing pre with
  | nil =>
    refine .cons (.pop rfl) ?_
    simp only [List.append_nil, pair, frame, List.head?_nil, List.tail_nil, Option.map_none, update_value]
    exact .nil ..
  | cons b rest ih =>
    rw [show 3*(b::rest).length+1 = ((3*rest.length+1)+1)+1+1 by simp; omega]
    refine .cons (.pop rfl) ?_
    simp only [pair, frame, List.head?_cons, List.tail_cons, Option.map_some, update_value]
    refine .cons (.push rfl) ?_
    simp only [pair, frame, update_history]
    refine .cons (.push rfl) ?_
    simpa only [append_bit, List.cons_append, List.append_assoc, List.nil_append, update_history,
      pair, frame] using ih (pre ++ [b])

private theorem writer_runs (value history : List Bool) :
    writer.Runs (3*value.length+2) (pair value history) (pair [] (fieldBits value ++ history)) := by
  refine .cons (.push rfl) ?_
  rw [update_history]
  exact scan_runs value [] history

private theorem reader_runs (value history old : List Bool) :
    (readField ()).Runs (3*value.length+1) (pair old (fieldBits value ++ history))
      (pair (value ++ old) history) := by
  have he : Function.update (fun _ : Unit => old) () (value ++ old) = fun _ => value ++ old := by
    funext i; cases i; rfl
  simpa only [pair, he] using readField_runs () value history (fun _ : Unit => old)

/-- The ten live-field ports together with the ten corresponding history ports. -/
abbrev Port := Fin 10 ⊕ Fin 10

private def fieldPorts (i : Fin 10) : Option Unit → Port
  | none => .inr i
  | some () => .inl i

private theorem fieldPorts_injective (i : Fin 10) : Function.Injective (fieldPorts i) := by
  intro a b h
  cases a <;> cases b <;> simp_all [fieldPorts]

/-- Move the live field at index `i` into its history stack using the frame-field encoding. -/
def pushField (i : Fin 10) : FiniteRoutine Port := (FiniteRoutine.ofRoutine writer).onPorts (fieldPorts i)

/-- Restore the most recently saved field at index `i` from its history stack. -/
def popField (i : Fin 10) : FiniteRoutine Port :=
  (FiniteRoutine.ofRoutine (readField ())).onPorts (fieldPorts i)

/-- Combine the live and history banks into the stack state of the frame store. -/
def registers (live history : Fin 10 → List Bool) : Stacks Port := Sum.elim live history

/-- Move one live field to its history, preserving every other field. -/
theorem pushField_runs (i : Fin 10) (live hist : Fin 10 → List Bool) :
    (pushField i).Runs (3*(live i).length+2) (registers live hist)
      (registers (Function.update live i []) (Function.update hist i (fieldBits (live i) ++ hist i))) := by
  apply FiniteRoutine.runs_onPorts_framed _ (fieldPorts_injective i) (writer_runs ..)
  · intro k; cases k <;> rfl
  · intro k; cases k <;> simp [registers, fieldPorts, pair, frame]
  · intro j hj
    cases j with
    | inl j => exact Function.update_of_ne (show j ≠ i from fun he => hj (some ()) (congrArg Sum.inl he.symm)) ..
    | inr j => exact Function.update_of_ne (show j ≠ i from fun he => hj none (congrArg Sum.inr he.symm)) ..

/-- Restore the top self-delimiting field and retain the rest of its history. -/
theorem popField_runs (i : Fin 10) (live hist : Fin 10 → List Bool) (value tail : List Bool)
    (h : hist i = fieldBits value ++ tail) :
    (popField i).Runs (3*value.length+1) (registers live hist)
      (registers (Function.update live i (value ++ live i)) (Function.update hist i tail)) := by
  apply FiniteRoutine.runs_onPorts_framed _ (fieldPorts_injective i) (reader_runs value tail (live i))
  · intro k; cases k with
    | none => exact h
    | some => rfl
  · intro k; cases k <;> simp [registers, fieldPorts, pair, frame]
  · intro j hj
    cases j with
    | inl j => exact Function.update_of_ne (show j ≠ i from fun he => hj (some ()) (congrArg Sum.inl he.symm)) ..
    | inr j => exact Function.update_of_ne (show j ≠ i from fun he => hj none (congrArg Sum.inr he.symm)) ..

end RankQuery.Stack.FrameStore

end VPVNP
end Computability
end OAI
