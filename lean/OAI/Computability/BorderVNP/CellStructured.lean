import OAI.Computability.BorderVNP.CellStackTape
import OAI.Computability.RationalHitting.StackWords
import OAI.Computability.VPVNP.RAMTapeISAPorts

/-! # Lowering binary stack procedures to the signed cell machine

The descriptor reader can use the project's structured list and binary arithmetic programs.
This translation implements their nondestructive tests with a pop followed by a push and
preserves ordinary successful returns. Its constant overhead is independent of the syntax.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Structured

open VPVNP.RAMTape RationalHitting.StackLanguage

variable {K : Type} [DecidableEq K]

private def push (k : K) (b : Bool) : FiniteRoutine K := .ofRoutine (.push k b)
private def pop (k : K) : FiniteRoutine K := .ofRoutine (Q := Unit) ⟨(), fun _ => .pop k fun _ => none⟩

private def test (k : K) (empty low high : FiniteRoutine K) : FiniteRoutine K :=
  .ofRoutine (Routine.popCase k empty.body ((push k false).followedBy low).body
    ((push k true).followedBy high).body)

private def loop (k : K) (body : FiniteRoutine K) : FiniteRoutine K :=
  .ofRoutine (Routine.popLoop k (fun _ => true)
    ((push k false).followedBy body).body ((push k true).followedBy body).body)

/-- Compile any structured deterministic stack procedure into finite named controls. -/
def lower : Program K → FiniteRoutine K
  | .skip => .ret
  | .push k b => push k b
  | .drop k => pop k
  | .transfer a b => .ofRoutine (Routine.popCase a .ret (.push b false) (.push b true))
  | .seq p q => (lower p).followedBy (lower q)
  | .branch k p q r => test k (lower p) (lower q) (lower r)
  | .loop k p => loop k (lower p)

private theorem restore_head (s : Stacks K) (k : K) (b : Bool) (l : List Bool)
    (hs : s k = b :: l) :
    (push k b).Runs 1 (Function.update s k l) s := by
  have h := Routine.runs_push k b (Function.update s k l)
  simpa only [push, FiniteRoutine.ofRoutine, Function.update_self, Function.update_idem, ← hs, Function.update_eq_self] using h

private theorem test_empty {p q r : FiniteRoutine K} {k : K} {s v : Stacks K} {t : ℕ}
    (hs : s k = []) (h : p.Runs t s v) : (test k p q r).Runs (t+1) s v :=
  Routine.runs_popCase_empty _ _ _ _ hs h

private theorem test_false {p q r : FiniteRoutine K} {k : K} {s v : Stacks K} {t : ℕ}
    {l : List Bool} (hs : s k = false :: l) (h : q.Runs t s v) : (test k p q r).Runs (1+t+1) s v :=
  Routine.runs_popCase_false _ _ _ _ hs ((restore_head _ _ _ _ hs).followedBy h)

private theorem test_true {p q r : FiniteRoutine K} {k : K} {s v : Stacks K} {t : ℕ}
    {l : List Bool} (hs : s k = true :: l) (h : r.Runs t s v) : (test k p q r).Runs (1+t+1) s v :=
  Routine.runs_popCase_true _ _ _ _ hs ((restore_head _ _ _ _ hs).followedBy h)

private theorem loop_empty (k : K) (p : FiniteRoutine K) (s : Stacks K) (hs : s k = []) :
    (loop k p).Runs 1 s s := by
  refine StackRuns.cons (.pop rfl) ?_
  have hu : Function.update s k [] = s := by rw [← hs, Function.update_eq_self]
  simp only [hs, List.head?_nil, List.tail_nil, hu]
  exact .nil ..

private theorem loop_cons (k : K) (p : FiniteRoutine K) {s u v : Stacks K} {a d : ℕ}
    {b : Bool} {xs : List Bool} (hs : s k = b :: xs)
    (hp : p.Runs a s u) (hl : (loop k p).Runs d u v) :
    (loop k p).Runs ((1+a)+d+1) s v := by
  let r := (loop k p).body
  have h := (restore_head _ _ _ _ hs).followedBy hp
  cases b with
  | false =>
    have entered := h.link r (Sum.inr ∘ Sum.inl) (some r.entry) (fun _ => rfl)
    refine .cons (.pop rfl) ?_
    simp only [hs, List.head?_cons, List.tail_cons]
    exact entered.trans hl
  | true =>
    have entered := h.link r (Sum.inr ∘ Sum.inr) (some r.entry) (fun _ => rfl)
    refine .cons (.pop rfl) ?_
    simp only [hs, List.head?_cons, List.tail_cons]
    exact entered.trans hl

/-- Every checked structured program evaluation executes as actual elementary stack steps,
with at most two elementary instructions per structured step. -/
theorem run {p : Program K} {s v : Stacks K} {t : ℕ} (h : Eval p s v t) :
    ∃ d ≤ 2*t, (lower p).Runs d s v := by
  induction h with
  | skip => exact ⟨1, by decide, Routine.runs_ret _⟩
  | push => exact ⟨1, by decide, Routine.runs_push ..⟩
  | drop => exact ⟨1, by decide, .cons (.pop rfl) (.nil ..)⟩
  | transfer a b s =>
    cases hs : s a with
    | nil =>
      exact ⟨2, le_rfl, Routine.runs_popCase_empty _ _ _ _ hs
        (by simpa [transfer, hs] using Routine.runs_ret s)⟩
    | cons x xs =>
      cases x
      · exact ⟨2, le_rfl, Routine.runs_popCase_false _ _ _ _ hs
          (by simpa [transfer, hs] using Routine.runs_push b false (Function.update s a xs))⟩
      · exact ⟨2, le_rfl, Routine.runs_popCase_true _ _ _ _ hs
          (by simpa [transfer, hs] using Routine.runs_push b true (Function.update s a xs))⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨a, ha, hr⟩ := ih₁
    obtain ⟨b, hb, hs⟩ := ih₂
    exact ⟨a+b, by omega, hr.followedBy hs⟩
  | branchNone hs _ ih =>
    obtain ⟨d, hd, hr⟩ := ih
    exact ⟨d+1, by omega, test_empty hs hr⟩
  | branchFalse hs _ ih =>
    obtain ⟨d, hd, hr⟩ := ih
    exact ⟨1+d+1, by omega, test_false hs hr⟩
  | branchTrue hs _ ih =>
    obtain ⟨d, hd, hr⟩ := ih
    exact ⟨1+d+1, by omega, test_true hs hr⟩
  | whileNil hs => exact ⟨1, by decide, loop_empty _ _ _ hs⟩
  | whileCons hs _ _ ih₁ ih₂ =>
    obtain ⟨a, ha, hr⟩ := ih₁
    obtain ⟨b, hb, ht⟩ := ih₂
    obtain ⟨bit, xs, he⟩ := List.exists_cons_of_ne_nil hs
    exact ⟨(1+a)+b+1, by omega, loop_cons _ _ he hr ht⟩

end CellMacro.Structured

end BorderVNP
end Computability
end OAI
