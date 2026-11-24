import OAI.Computability.VPVNP.RankQueryStackNativeFrames

/-! # Bank conventions at deterministic Schur subroutine boundaries -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Engine

open RAMTape Evaluator.InputBank

variable {n U Z p e : ℕ} {c : SliceArithmetic.Vector p e} {K : Type}

/-- Abstract control of the evaluator specialized to Schur keys and encoded scalars. -/
abbrev Ctl (n U Z : ℕ) (c : SliceArithmetic.Vector p e) := Control (Key n U Z) (Scalar c)
/-- Abstract configuration of the Schur evaluator, including its stack of pending frames. -/
abbrev Cfg (n U Z : ℕ) (c : SliceArithmetic.Vector p e) := Config (Key n U Z) (Scalar c)

/-- Live register contents for an abstract control, encoding the query, scan count and
accumulator when needed. -/
def live (w v : ℕ) : Ctl n U Z c → Data
  | .enter q => fields w [] q [] [] []
  | .scan q k a => fields w [] q (UniversalCountStack.digits w k) (scalar v a) []
  | .returned _ => fun _ => []

/-- Encoded scalar on the result port of a returning control, and an empty result port during
evaluation. -/
def output (v : ℕ) : Ctl n U Z c → List Bool
  | .returned a => scalar v a
  | _ => []

/-- Assemble live registers, saved frames, condition bits, result and auxiliary stacks at a
control boundary. -/
def atControl (w v : ℕ) (ctl : Ctl n U Z c) (fs : List (F n U Z c)) (aux : Stacks K)
    (signal : List Bool := []) : Stacks (Port K) :=
  store (live w v ctl) (history w v fs) signal (output v ctl) aux

/-- Physical engine entry state corresponding to an abstract enter, scan or return control. -/
def label (a : Actions K) : Ctl n U Z c → State a
  | .enter _ => invoke a .describe
  | .scan .. => invoke a .scan
  | .returned _ => .inl .returned

/-- Restored live-frame data after the engine has consumed the saved direction tag in field
zero. -/
def popped (w v : ℕ) (f : F n U Z c) : Data := Function.update (nativeFrame w v f) 0 []

variable [DecidableEq K] [Fact p.Prime] [NeZero e]

/-- Physical run contracts of the five arithmetic and routing subprograms.
The engine implements the two frame operations itself. A pending state carries
the computed child query in the dispatch output registers. -/
structure Contracts (a : Actions K) (prog : Program (Key n U Z) (Scalar c)) (w v B lim : ℕ)
    (ready : Stacks K → Prop) (pending : Key n U Z → Stacks K → Prop) (describeBudget : ℕ := B) : Prop where
  describe (q : Key n U Z) (fs : List (F n U Z c)) (aux : Stacks K) : ready aux →
    ∃ t ≤ describeBudget, ∃ out, ready out ∧ a.describe.Runs t (atControl w v (.enter q) fs aux)
      (match prog.describe q with
       | .inl r => atControl w v (.returned r) fs out [true]
       | .inr k => atControl w v (.scan q k 0) fs out [false])
  scanZero (q : Key n U Z) (acc : Scalar c) (fs : List (F n U Z c)) (aux : Stacks K) : ready aux →
    ∃ t ≤ B, ∃ out, ready out ∧ a.scan.Runs t (atControl w v (.scan q 0 acc) fs aux)
      (atControl w v (.returned acc) fs out [true])
  scanSucc (q : Key n U Z) (k : ℕ) (acc : Scalar c) (fs : List (F n U Z c)) (aux : Stacks K) :
    k+1 ≤ lim → (∃ t, prog.describe q = .inr t ∧ k < t) → ready aux →
    ∃ t ≤ B, ∃ out, pending (prog.left q k) out ∧ a.scan.Runs t (atControl w v (.scan q (k+1) acc) fs aux)
      (store (nativeFrame w v (.left q k acc)) (history w v fs) [false] [] out)
  activate (q : Key n U Z) (fs : List (F n U Z c)) (aux : Stacks K) : pending q aux →
    ∃ t ≤ B, ∃ out, ready out ∧ a.activate.Runs t (store (fun _ => []) (history w v fs) [] [] aux)
      (atControl w v (.enter q) fs out)
  right (q : Key n U Z) (k : ℕ) (acc l : Scalar c) (fs : List (F n U Z c)) (aux : Stacks K) :
    k < lim → (∃ t, prog.describe q = .inr t ∧ k < t) → ready aux →
    ∃ t ≤ B, ∃ out, pending (prog.right q k) out ∧ a.right.Runs t
      (store (popped w v (.left q k acc)) (history w v fs) [] (scalar v l) aux)
      (store (nativeFrame w v (.right q k acc l)) (history w v fs) [] [] out)
  multiplyAdd (q : Key n U Z) (k : ℕ) (acc l r : Scalar c) (fs : List (F n U Z c)) (aux : Stacks K) :
    k < lim → ready aux →
    ∃ t ≤ B, ∃ out, ready out ∧ a.multiplyAdd.Runs t
      (store (popped w v (.right q k acc l)) (history w v fs) [] (scalar v r) aux)
      (atControl w v (.scan q k (acc+l*r)) fs out)

/-- The active scan count is at most `lim` and each suspended frame's remaining index is
strictly below `lim`. -/
def InRange (lim : ℕ) (cfg : Cfg n U Z c) : Prop :=
  (match cfg.1 with | .scan _ k _ => k ≤ lim | _ => True) ∧ ∀ f ∈ cfg.2, f.remaining < lim

omit [DecidableEq K] in
theorem inRange_step (prog : Program (Key n U Z) (Scalar c)) (lim : ℕ) (hp : prog.ArityLE lim)
    (cfg : Cfg n U Z c) (h : InRange lim cfg) : InRange lim (prog.step cfg) := by
  obtain ⟨ctl, fs⟩ := cfg
  cases ctl with
  | enter q =>
    cases he : prog.describe q with
    | inl r => exact ⟨by simp [Program.step, he], by simpa [Program.step, he] using h.2⟩
    | inr k => exact ⟨by simpa [Program.step, he] using hp q k he, by simpa [Program.step, he] using h.2⟩
  | scan q k a =>
    cases k with
    | zero => exact ⟨trivial, h.2⟩
    | succ k =>
      refine ⟨trivial, ?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with eq | hm
      · subst f; exact h.1
      · exact h.2 _ hm
  | returned r =>
    cases fs with
    | nil => exact h
    | cons f fs =>
      have hk := h.2 f List.mem_cons_self
      cases f with
      | left q k a =>
        refine ⟨trivial, ?_⟩
        intro j hj
        rcases List.mem_cons.mp hj with eq | hm
        · subst j; exact hk
        · exact h.2 _ (List.mem_cons_of_mem _ hm)
      | right q k a l =>
        exact ⟨Nat.le_of_lt hk, fun j hj => h.2 _ (List.mem_cons_of_mem _ hj)⟩

/-- A suspended frame retains a legal child index of its own parent. This
ensures the physical child dispatcher only sees indices in its node's arity. -/
def CursorRange (prog : Program (Key n U Z) (Scalar c)) (cfg : Cfg n U Z c) : Prop :=
  (match cfg.1 with | .scan q k _ => ∃ t, prog.describe q = .inr t ∧ k ≤ t | _ => True) ∧
  ∀ f ∈ cfg.2, match f with
    | .left q k _ | .right q k _ _ => ∃ t, prog.describe q = .inr t ∧ k < t

omit [DecidableEq K] [Fact p.Prime] [NeZero e] in
theorem cursorRange_step (prog : Program (Key n U Z) (Scalar c)) [Semiring (Scalar c)]
    (cfg : Cfg n U Z c) (h : CursorRange prog cfg) : CursorRange prog (prog.step cfg) := by
  obtain ⟨ctl, fs⟩ := cfg
  cases ctl with
  | enter q =>
    cases he : prog.describe q with
    | inl r => exact ⟨by simp [Program.step, he], by simpa [Program.step, he] using h.2⟩
    | inr k =>
      have hg : prog.step (.enter q,fs) = (.scan q k 0,fs) := by simp [Program.step, he]
      rw [hg]; exact ⟨⟨k,he,le_rfl⟩,h.2⟩
  | scan q k a =>
    cases k with
    | zero => exact ⟨trivial, h.2⟩
    | succ k =>
      refine ⟨trivial, fun f hf => ?_⟩
      rcases List.mem_cons.mp hf with eq | hm
      · subst f; exact h.1
      · exact h.2 _ hm
  | returned r =>
    cases fs with
    | nil => exact h
    | cons f fs =>
      have hk := h.2 f List.mem_cons_self
      cases f with
      | left q k a =>
        refine ⟨trivial, fun j hj => ?_⟩
        rcases List.mem_cons.mp hj with eq | hm
        · subst j; exact hk
        · exact h.2 _ (List.mem_cons_of_mem _ hm)
      | right q k a l =>
        obtain ⟨t,ht,hle⟩ := hk
        exact ⟨⟨t,ht,Nat.le_of_lt hle⟩, fun j hj => h.2 _ (List.mem_cons_of_mem _ hj)⟩

end RankQuery.Stack.Engine

end VPVNP
end Computability
end OAI
