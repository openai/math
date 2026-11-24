import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.StructuredStackLoop

/-! # Moving one word of a sort block onto a reverse buffer

The input and buffer hold arbitrary bits. A separate unary word-width stack
is restored after the move so the same finite control can read all five
fields of a record and all records before the selected slot.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortGather

/-- Gather ports for the record block, unary offset and width, reversible width counter,
skipped and selected buffers and output. -/
inductive Port where
  | block | offset | width | widthBack | saved | recordBack | output
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

namespace WordMove

/-- The word mover's source block, reversible width tally and reverse destination buffer. -/
inductive Port where
  | block | width | widthBack | dest
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Control for moving a fixed-width word bit by bit, saving width markers, then restoring the
width tally. -/
inductive Phase where
  | tick | read | save (b : Bool) | mark | rewind | put | done | reject
  deriving DecidableEq, Fintype

/-- Use one width marker per bit moved from the block to the destination and restore all
markers at the end of the word. -/
def code : StackCode Port Phase
  | .tick => .pop .width fun m => m.elim .rewind fun _ => .read
  | .read => .pop .block fun b => b.elim .reject .save
  | .save b => .push .dest b .mark
  | .mark => .push .widthBack true .tick
  | .rewind => .pop .widthBack fun m => m.elim .done fun _ => .put
  | .put => .push .width true .rewind
  | .done => .halt true
  | .reject => .halt false

private def bank (block width back dest : List Bool) : Stacks Port
  | .block => block
  | .width => width
  | .widthBack => back
  | .dest => dest

private theorem update_bank (block width back dest val : List Bool) (p : Port) :
    Function.update (bank block width back dest) p val = match p with
      | .block => bank val width back dest
      | .width => bank block val back dest
      | .widthBack => bank block width val dest
      | .dest => bank block width back val := by
  funext j
  cases p <;> cases j <;> rfl

local macro "move_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [bank, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none, update_bank])

private theorem collect (data tail back dst : List Bool) :
    StackRuns code (4 * data.length + 1) .tick
      (bank (data ++ tail) (List.replicate data.length true) back dst)
      .rewind (bank tail [] (List.replicate data.length true ++ back) (data.reverse ++ dst)) := by
  induction data generalizing back dst with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.nil_append, List.reverse_nil,
      List.replicate_zero]
    move_step
    exact .nil ..
  | cons b bs ih =>
    simp only [List.length_cons, Nat.mul_succ, List.cons_append, List.reverse_cons,
      List.append_assoc]
    rw [List.replicate_succ (n := bs.length)]
    move_step
    move_step
    move_step
    move_step
    have hr := ih (true :: back) (b :: dst)
    rw [← List.singleton_append (x := true), ← List.append_assoc, ← List.replicate_succ', List.replicate_succ] at hr
    exact hr

private theorem restore (block width dest : List Bool) (n : ℕ) :
    StackRuns code (2*n+1) .rewind (bank block width (List.replicate n true) dest) .done
      (bank block (List.replicate n true ++ width) [] dest) := by
  induction n generalizing width with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.zero_add]
    move_step
    exact .nil ..
  | succ n ih =>
    rw [Nat.mul_succ, List.replicate_succ (n := n)]
    move_step
    move_step
    have hr := ih (true :: width)
    rw [← List.singleton_append (x := true), ← List.append_assoc, ← List.replicate_succ', List.replicate_succ] at hr
    exact hr

theorem runs (s : Stacks Port) (data tail : List Bool)
    (hb : s .block = data ++ tail) (hw : s .width = List.replicate data.length true)
    (ht : s .widthBack = []) :
    StackRuns code (6*data.length+2) .tick s .done
      (Function.update (Function.update s .block tail) .dest (data.reverse ++ s .dest)) := by
  have h₁ := collect data tail [] (s .dest)
  have h₂ := restore tail [] (data.reverse ++ s .dest) data.length
  simp only [List.append_nil] at h₁ h₂
  have hs : bank (data ++ tail) (List.replicate data.length true) [] (s .dest) = s := by
    funext p
    cases p <;> simp [bank, hb, hw, ht]
  have hu : bank tail (List.replicate data.length true) [] (data.reverse ++ s .dest) =
      Function.update (Function.update s .block tail) .dest (data.reverse ++ s .dest) := by
    funext p
    cases p <;> simp [bank, hw, ht]
  rw [hs] at h₁
  rw [hu] at h₂
  convert h₁.trans h₂ using 1
  omega

end WordMove

/-- Distinguish a word from a skipped record from one belonging to the selected record. -/
inductive Buffer where
  | skipped | selected
  deriving DecidableEq

/-- Use the saved-prefix port for skipped words and the selected-record reverse buffer for
selected words. -/
def Buffer.dest : Buffer → Port
  | .skipped => .saved
  | .selected => .recordBack

private def wordPorts (b : Buffer) : WordMove.Port → Port
  | .block => .block
  | .width => .width
  | .widthBack => .widthBack
  | .dest => b.dest

private theorem injective_wordPorts (b : Buffer) : Function.Injective (wordPorts b) := by
  intro i j h
  cases b <;> cases i <;> cases j <;> first | rfl | cases h

/-- Move one width-delimited word from the current block to the named reverse buffer. -/
def word (b : Buffer) : FiniteRoutine Port :=
  .ofStackCode WordMove.code (wordPorts b) .tick fun q => decide (q = .done)

theorem word_runs (b : Buffer) (s : Stacks Port) (data tail : List Bool)
    (hb : s .block = data ++ tail) (hw : s .width = List.replicate data.length true)
    (ht : s .widthBack = []) :
    (word b).Runs (6*data.length+2) s
      (Function.update (Function.update s .block tail) b.dest (data.reverse ++ s b.dest)) := by
  let small := s ∘ wordPorts b
  unfold word
  apply FiniteRoutine.runs_ofStackCode_framed (src := WordMove.code) (injective_wordPorts b)
    (normal := fun q => decide (q = .done)) (entry := .tick) (exit := .done) rfl rfl
    (fun q h => by have hq : q = .done := of_decide_eq_true h; subst q; rfl)
    (WordMove.runs small data tail hb hw ht) (fun _ => rfl)
  · intro i
    cases b <;> cases i <;> simp [wordPorts, Buffer.dest, small]
  · intro j hj
    simp [show j ≠ b.dest from Ne.symm (hj .dest), show j ≠ .block from Ne.symm (hj .block)]

end RAMTape.SortGather

end VPVNP
end Computability
end OAI
