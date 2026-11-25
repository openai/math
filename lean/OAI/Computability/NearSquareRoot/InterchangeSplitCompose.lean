import OAI.Computability.NearSquareRoot.ShortWordSpace

/-!
# Sequential fixed-tape machines

When the first rule halts, a single transition preserves all symbols and head
positions and enters the second machine. Both phases use the same tapes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace TapeSequence

open IntegerMultiplication

variable {A Q R I : Type}

/-- Tag a control state while leaving each physical tape intact. -/
def relabel {S T : Type} (f : S → T) (c : TM.Config A S I) : TM.Config A T I :=
  ⟨f c.pc, c.tape⟩

/-- Run the first machine until it halts, then start the second at `entry`. -/
def rule (m : TM.Rule A Q I) (n : TM.Rule A R I) (entry : R) : TM.Rule A (Q ⊕ R) I
  | .inl q, read =>
    match m q read with
    | some (q', op) => some (.inl q', op)
    | none => some (.inr entry, fun i => (read i, .stay))
  | .inr r, read => (n r read).map (fun (r', op) => (.inr r', op))

private theorem stay_same (T : TM.Tape A) : T.apply (T.view 0, .stay) = T := by
  cases T with
  | mk p v =>
    simp only [TM.Tape.apply, TM.Move.shift, add_zero, TM.Tape.mk.injEq, true_and]
    funext i
    split_ifs with h
    · rw [h]
    · rfl

variable (m : TM.Rule A Q I) (n : TM.Rule A R I) (entry : R)

private theorem first_step {c d : TM.Config A Q I} (h : TM.advance m c = some d) :
    TM.advance (rule m n entry) (relabel Sum.inl c) = some (relabel Sum.inl d) := by
  unfold TM.advance at *
  cases e : m c.pc (fun i => (c.tape i).view 0) with
  | none => simp [e] at h
  | some action =>
    rcases action with ⟨q, op⟩
    simp only [e, Option.map_some, Option.some.injEq] at h
    subst d
    simp [relabel, rule, e]

theorem first_trace {c d : TM.Config A Q I} {t : ℕ} (h : Trace (TM.advance m) c t d) :
    Trace (TM.advance (rule m n entry)) (relabel Sum.inl c) t (relabel Sum.inl d) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (first_step m n entry hs) ih

/-- Account for the transition that passes control between phases. -/
theorem handoff {c : TM.Config A Q I} (h : TM.advance m c = none) :
    TM.advance (rule m n entry) (relabel Sum.inl c) =
      some ⟨Sum.inr entry, c.tape⟩ := by
  have e : m c.pc (fun i => (c.tape i).view 0) = none := by
    simpa [TM.advance] using h
  simp [TM.advance, rule, relabel, e, stay_same]

private theorem second_step (c : TM.Config A R I) :
    TM.advance (rule m n entry) (relabel Sum.inr c) =
      (TM.advance n c).map (relabel Sum.inr) := by
  unfold TM.advance
  cases e : n c.pc (fun i => (c.tape i).view 0) <;> simp [relabel, rule, e]

theorem second_trace {c d : TM.Config A R I} {t : ℕ} (h : Trace (TM.advance n) c t d) :
    Trace (TM.advance (rule m n entry)) (relabel Sum.inr c) t (relabel Sum.inr d) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (by rw [second_step, hs]; rfl) ih

/-- A complete run of the two machines, charging exactly one extra step.
The second starts with the absolute contents and head positions left by the first. -/
theorem run {a b : TM.Config A Q I} {c : TM.Config A R I} {s t : ℕ}
    (first : Trace (TM.advance m) a s b) (haltFirst : TM.advance m b = none)
    (second : Trace (TM.advance n) ⟨entry, b.tape⟩ t c) (haltSecond : TM.advance n c = none) :
    Trace (TM.advance (rule m n entry)) (relabel Sum.inl a) (s + 1 + t) (relabel Sum.inr c) ∧
      TM.advance (rule m n entry) (relabel Sum.inr c) = none := by
  refine ⟨((first_trace m n entry first).trans (.single (handoff m n entry haltFirst))).trans
    (second_trace m n entry second), ?_⟩
  rw [second_step, haltSecond]
  rfl

/-- Transport a fence through a control-only relabeling that preserves traces
up to their original terminal time. -/
private theorem relabel_fenced {S T : Type} {lo hi : I → ℤ}
    {p : TM.Rule A S I} {p' : TM.Rule A T I} (f : S → T)
    (liftTrace : ∀ {x y t}, Trace (TM.advance p) x t y →
      Trace (TM.advance p') (relabel f x) t (relabel f y))
    {x y t} (h : FencedRun p lo hi x t y) :
    FencedRun p' lo hi (relabel f x) t (relabel f y) := by
  refine ⟨liftTrace h.1, fun u hu c hx i => ?_⟩
  obtain ⟨d, hd, _⟩ := trace_split h.1 hu
  rw [trace_endpoint_unique hx (liftTrace hd)]
  exact h.2 u hu d hd i

/-- A common fence for both phases also bounds the handoff and the whole
composite trace, so its cell count is independent of the number of passes. -/
theorem run_fenced {lo hi : I → ℤ} {a b : TM.Config A Q I} {c : TM.Config A R I} {s t : ℕ}
    (first : FencedRun m lo hi a s b) (haltFirst : TM.advance m b = none)
    (second : FencedRun n lo hi ⟨entry, b.tape⟩ t c) :
    FencedRun (rule m n entry) lo hi (relabel Sum.inl a) (s + 1 + t) (relabel Sum.inr c) := by
  have switched := Trace.single (handoff m n entry haltFirst)
  have handoffs : FencedRun (rule m n entry) lo hi (relabel Sum.inl b) 1
      (relabel Sum.inr ⟨entry, b.tape⟩) := by
    refine ⟨switched, fun u hu d h i => ?_⟩
    obtain rfl | rfl : u = 0 ∨ u = 1 := by omega
    · rw [trace_endpoint_unique h (.nil _)]
      exact first.2 s (by omega) b first.1 i
    · rw [trace_endpoint_unique h switched]
      exact first.2 s (by omega) b first.1 i
  exact ((relabel_fenced Sum.inl (first_trace m n entry) first).trans handoffs).trans
    (relabel_fenced Sum.inr (second_trace m n entry) second)

end TapeSequence

end NearSquareRoot
end Computability
end OAI
