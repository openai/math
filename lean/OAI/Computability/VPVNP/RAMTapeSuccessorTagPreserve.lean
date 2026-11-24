import OAI.Computability.VPVNP.RAMTapeSuccessorTags

/-!
# Reading a successor tag and restoring the input word

After classifying each bit, push it onto the temporary stack. Once the tag
has been decided, transfer those bits back. The caller receives the tag in
finite control and can still read the whole word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SuccessorTags

open TapeWord

/-- States for classifying a word while saving its bits, then restoring them with the tag held
in control. -/
inductive KeepState where
  | read (q : State)
  | save (q : State) (bit : Bool)
  | restore (tag : Tag)
  | put (tag : Tag) (bit : Bool)
  | done (tag : Tag)
  deriving DecidableEq, Fintype

variable {K : Type*}

/-- Classify the source word, move its bits back from scratch, and finish with its tag in
finite control. -/
def codeKeep (src tmp : K) : StackCode K KeepState
  | .read q => .pop src fun bit => bit.elim (.restore (finish q)) fun b => .save (advance q b) b
  | .save q b => .push tmp b (.read q)
  | .restore t => .pop tmp fun bit => bit.elim (.done t) (.put t)
  | .put t b => .push src b (.restore t)
  | .done _ => .halt true

variable [DecidableEq K] {src tmp : K}

private def pair (base : Stacks K) (src tmp : K) (input scratch : List Bool) : Stacks K :=
  Function.update (Function.update base src input) tmp scratch

private theorem source_get (hne : src ≠ tmp) (base : Stacks K) (x y : List Bool) :
    pair base src tmp x y src = x := by simp [pair, Function.update_of_ne hne]

private theorem scratch_get (base : Stacks K) (x y : List Bool) :
    pair base src tmp x y tmp = y := by simp [pair]

private theorem source_write (hne : src ≠ tmp) (base : Stacks K) (x y z : List Bool) :
    Function.update (pair base src tmp x y) src z = pair base src tmp z y := by
  simp only [pair]
  rw [Function.update_comm hne.symm, Function.update_idem]

private theorem scratch_write (base : Stacks K) (x y z : List Bool) :
    Function.update (pair base src tmp x y) tmp z = pair base src tmp x z := by simp [pair]

local macro "keep_step " h:ident : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [source_get $h, scratch_get, source_write $h, scratch_write, List.head?_cons,
    List.tail_cons, List.head?_nil, List.tail_nil, Option.elim_some, Option.elim_none])

private theorem save_run (hne : src ≠ tmp) (base : Stacks K) (q : State) (x y : List Bool) :
    StackRuns (codeKeep src tmp) (2*x.length+1) (.read q) (pair base src tmp x y)
      (.restore (finish (x.foldl advance q))) (pair base src tmp [] (x.reverse ++ y)) := by
  induction x generalizing q y with
  | nil => keep_step hne; exact .nil ..
  | cons b x ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.foldl_cons]
    keep_step hne
    keep_step hne
    exact ih (advance q b) (b :: y)

private theorem restore_run (hne : src ≠ tmp) (base : Stacks K) (t : Tag) (x y : List Bool) :
    StackRuns (codeKeep src tmp) (2*y.length+1) (.restore t) (pair base src tmp x y)
      (.done t) (pair base src tmp (y.reverse ++ x) []) := by
  induction y generalizing x with
  | nil => keep_step hne; exact .nil ..
  | cons b y ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    keep_step hne
    keep_step hne
    exact ih (b :: x)

/-- Classify the source using an empty scratch stack. The two passes restore
all stacks after exactly four instructions per bit and two empty pops. -/
theorem keep_run (src tmp : K) (hne : src ≠ tmp) (s : Stacks K) (ht : s tmp = []) :
    StackRuns (codeKeep src tmp) (4*(s src).length+2) (.read .first) s
      (.done (Tag.ofNat (value (s src)))) s := by
  have hs := save_run hne s .first (s src) []
  have hr := restore_run hne s (Tag.ofNat (value (s src))) [] (s src).reverse
  have hpair : pair s src tmp (s src) [] = s := by
    simp [pair, ← ht]
  simp only [finish_fold, List.append_nil, List.length_reverse, List.reverse_reverse, hpair] at hs hr
  convert hs.trans hr using 1
  omega

end RAMTape.SuccessorTags

end VPVNP
end Computability
end OAI
