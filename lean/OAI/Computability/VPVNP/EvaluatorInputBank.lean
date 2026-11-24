import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.EvaluatorMatrixStep
import Mathlib.Tactic.DeriveFintype

/-!
# Loading evaluator advice and exponents from a binary input

Each fixed port receives a separate field. A zero tag ends the field and a one
tag precedes a payload bit. Sending payloads in reverse order puts the original
lists on their stacks with one push per bit. The parser's finite control is
fixed by the ordered port names, independently of field lengths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.InputBank

open RAMTape

private def tagged : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: tagged bs

/-- A self-delimiting raw input field. -/
def fieldBits (bs : List Bool) : List Bool := tagged bs.reverse

private theorem length_tagged (bs : List Bool) : (tagged bs).length = 2*bs.length+1 := by
  induction bs <;> simp [tagged, *]
  omega

theorem length_fieldBits (bs : List Bool) : (fieldBits bs).length = 2*bs.length+1 := by
  simp [fieldBits, length_tagged]

private theorem tagged_pair (xs : List Bool) (i : Fin xs.length) :
    (tagged xs)[2*i.val]'(by rw [length_tagged]; omega) = true ∧
      (tagged xs)[2*i.val+1]'(by rw [length_tagged]; omega) = xs[i.val] := by
  induction xs with
  | nil => exact i.elim0
  | cons b bs ih =>
    cases i using Fin.cases with
    | zero => exact ⟨rfl, rfl⟩
    | succ j =>
      simp only [Fin.val_succ, Nat.mul_succ, tagged, List.getElem_cons_succ]
      exact ih j

private theorem tagged_end (xs : List Bool) :
    (tagged xs)[2*xs.length]'(by rw [length_tagged]; omega) = false := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simpa only [List.length_cons, Nat.mul_succ, tagged, List.getElem_cons_succ] using ih

theorem fieldBits_tag (xs : List Bool) (i : Fin xs.length) :
    (fieldBits xs)[2*i.val]'(by rw [length_fieldBits]; omega) = true :=
  (tagged_pair xs.reverse ⟨i.val, by simp⟩).1

theorem fieldBits_payload (xs : List Bool) (i : Fin xs.length) :
    (fieldBits xs)[2*i.val+1]'(by rw [length_fieldBits]; omega) = xs.reverse[i.val]'(by simp) :=
  (tagged_pair xs.reverse ⟨i.val, by simp⟩).2

theorem fieldBits_end (xs : List Bool) :
    (fieldBits xs)[2*xs.length]'(by rw [length_fieldBits]; omega) = false := by
  simpa only [fieldBits, List.length_reverse] using tagged_end xs.reverse

/-- Finite control for reading tagged input fields and pushing each payload bit onto its named
stack. -/
inductive Phase where
  | tag | bit | push (b : Bool) | reject
  deriving DecidableEq, Fintype

/-- Port `none` contains the raw input. All output ports have the form
`some k`, so reading a field never overwrites an unread input bit. -/
def readField {K : Type} (k : K) : Routine (Option K) Phase where
  entry := .tag
  code
    | .tag => .pop none fun b ↦ match b with
      | none => some .reject | some false => none | some true => some .bit
    | .bit => .pop none fun b ↦ some (b.elim .reject .push)
    | .push b => .push (some k) b (some .tag)
    | .reject => .halt false

/-- Place the raw stream on the input stack and a bank on the output stacks. -/
def frame {K : Type} (raw : List Bool) (bank : Stacks K) : Stacks (Option K)
  | none => raw
  | some k => bank k

variable {K : Type} [DecidableEq K]

private theorem put_raw (raw raw' : List Bool) (bank : Stacks K) :
    Function.update (frame raw bank) none raw' = frame raw' bank := by
  funext k
  cases k <;> simp [frame]

private theorem put_port (raw bs : List Bool) (bank : Stacks K) (k : K) :
    Function.update (frame raw bank) (some k) bs = frame raw (Function.update bank k bs) := by
  funext j
  cases j with
  | none => simp [frame]
  | some i => by_cases h : i = k <;> simp [frame, h]

private theorem read_tagged (k : K) (bits tail : List Bool) (bank : Stacks K) :
    (readField k).Runs (3*bits.length+1) (frame (tagged bits ++ tail) bank)
      (frame tail (Function.update bank k (bits.reverse ++ bank k))) := by
  induction bits generalizing bank with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil, List.nil_append,
      Function.update_eq_self]
    apply StackRuns.cons (StackStep.pop (code := (readField k).standalone) rfl)
    simp only [frame, tagged, List.cons_append, List.nil_append, List.head?_cons, List.tail_cons, put_raw]
    exact .nil ..
  | cons b bits ih =>
    rw [show 3*(b::bits).length+1 = ((3*bits.length+1)+1)+1+1 by simp; omega]
    apply StackRuns.cons (StackStep.pop (code := (readField k).standalone) rfl)
    simp only [tagged, List.cons_append, frame, List.head?_cons, List.tail_cons, put_raw]
    apply StackRuns.cons (StackStep.pop (code := (readField k).standalone) rfl)
    simp only [frame, List.head?_cons, List.tail_cons, put_raw, Option.elim_some]
    apply StackRuns.cons (StackStep.push (code := (readField k).standalone) rfl)
    have h := ih (Function.update bank k (b::bank k))
    simp only [Function.update_self, Function.update_idem] at h
    simp only [frame, put_port, List.reverse_cons, List.append_assoc, List.singleton_append]
    exact h

/-- Reading one field consumes its terminator and leaves the next field at
the top of the input. It uses three instructions per bit and one for the tag. -/
theorem readField_runs (k : K) (bs tail : List Bool) (bank : Stacks K) :
    (readField k).Runs (3*bs.length+1) (frame (fieldBits bs ++ tail) bank)
      (frame tail (Function.update bank k (bs ++ bank k))) := by
  simpa [fieldBits] using read_tagged k bs.reverse tail bank

/-- The ordered fields are fixed when the input parser is compiled. -/
def reader : List K → FiniteRoutine (Option K)
  | [] => .ret
  | k :: ks => (FiniteRoutine.ofRoutine (readField k)).followedBy (reader ks)

/-- Raw binary serialization of the selected ports, in their specified order. -/
def rawInput (ks : List K) (data : Stacks K) : List Bool :=
  ks.flatMap (fun k ↦ fieldBits (data k))

private def load (data : Stacks K) : List K → Stacks K → Stacks K
  | [], bank => bank
  | k :: ks, bank => load data ks (Function.update bank k (data k ++ bank k))

private theorem reader_runs (ks : List K) (data bank : Stacks K) (tail : List Bool) :
    (reader ks).Runs ((ks.map (fun k ↦ 3*(data k).length+1)).sum+1)
      (frame (rawInput ks data ++ tail) bank) (frame tail (load data ks bank)) := by
  induction ks generalizing bank with
  | nil => exact Routine.runs_ret _
  | cons k ks ih =>
    have h := FiniteRoutine.Runs.followedBy (a := .ofRoutine (readField k))
      (readField_runs k (data k) (rawInput ks data ++ tail) bank) (ih _)
    simpa only [reader, rawInput, load, List.map_cons, List.sum_cons, List.flatMap_cons,
      List.append_assoc, Nat.add_assoc] using h

private theorem load_apply (ks : List K) (data bank : Stacks K) (hks : ks.Nodup) (k : K) :
    load data ks bank k = if k ∈ ks then data k ++ bank k else bank k := by
  induction ks generalizing bank with
  | nil => simp [load]
  | cons j ks ih =>
    rw [load, ih _ hks.of_cons]
    by_cases he : k = j
    · subst k
      simp [hks.notMem]
    · simp [he]

/-- From the raw input alone, restore the complete named evaluator bank.
Advice fields and runtime exponent fields have independent data and lengths. -/
theorem load_input_runs (ks : List K) (hks : ks.Nodup) (hall : ∀ k, k ∈ ks) (data : Stacks K) :
    (reader ks).Runs ((ks.map (fun k ↦ 3*(data k).length+1)).sum+1)
      (frame (rawInput ks data) (fun _ ↦ [])) (frame [] data) := by
  have h : load data ks (fun _ ↦ []) = data := by
    funext k
    simp only [load_apply ks data _ hks k, hall k, ite_true, List.append_nil]
  simpa only [List.append_nil, h] using reader_runs ks data (fun _ ↦ []) []

/-- Initially empty scratch stacks need no fields in the raw stream. -/
theorem load_selected_runs (ks : List K) (hks : ks.Nodup) (data : Stacks K)
    (outside : ∀ k, k ∉ ks → data k = []) :
    (reader ks).Runs ((ks.map (fun k ↦ 3*(data k).length+1)).sum+1)
      (frame (rawInput ks data) (fun _ ↦ [])) (frame [] data) := by
  have h : load data ks (fun _ ↦ []) = data := by
    funext k
    rw [load_apply ks data _ hks k]
    by_cases hk : k ∈ ks <;> simp [hk, outside]
  simpa only [List.append_nil, h] using reader_runs ks data (fun _ ↦ []) []

omit [DecidableEq K] in
/-- Encoding the advice block and the exponent block separately concatenates
their raw streams; changing an exponent does not change any advice field. -/
theorem rawInput_append (advice exponents : List K) (data : Stacks K) :
    rawInput (advice ++ exponents) data = rawInput advice data ++ rawInput exponents data :=
  List.flatMap_append ..

end Evaluator.InputBank

end VPVNP
end Computability
end OAI
