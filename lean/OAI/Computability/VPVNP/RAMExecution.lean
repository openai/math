import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic

/-!
# Bounded executions of burst RAM calls

The genuine interpreter follows a supplied sequence of binary choices and
answers external reads from memory. A processor in Lemma 10.1 instead guesses
each answer. The two executions agree exactly when all reads in its local
transcript have their prescribed values. Binary choices are retained even when
their two continuations coincide.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

/-- A width-`w` RAM word, represented by a natural number strictly below `2^w`. -/
abbrev Word (w : ℕ) := Fin (2 ^ w)
/-- External RAM storing a width-`w` word at each natural-number address. -/
abbrev Memory (w : ℕ) := ℕ → Word w

/-- A small step in a call. `finish none` accepts and `finish (some s)`
returns the persistent state for the next call. -/
inductive CallAction (w : ℕ) (C : Type*)
  | localStep (next : C)
  | branch (next : Bool → C)
  | read (address : Word w) (next : Word w → C)
  | write (address value : Word w) (next : C)
  | finish (result : Option (Word w))
  | reject

/-- A burst-RAM call program with a private configuration type, an initializer from the
persistent word and a one-step instruction function. -/
structure Program (w : ℕ) (C : Type*) where
  /-- Private state is recreated from the persistent word on every call. -/
  start : Word w → C
  /-- Select the next call action from the current private configuration. -/
  step : C → CallAction w C

/-- A recorded private tick, binary branch choice, external read or external write. Both kinds
of probe carry the address and word value. -/
inductive Event (w : ℕ)
  | tick
  | choice (bit : Bool)
  | read (address value : Word w)
  | write (address value : Word w)
  deriving DecidableEq

/-- A single call's ordered event trace and its optional persistent word for the next call. -/
structure Report (w : ℕ) where
  /-- Chronological sequence of private ticks, branch choices and external probes during the
  call. -/
  events : List (Event w)
  /-- Persistent word returned to start another call, or `none` when the machine accepts and
  stops. -/
  result : Option (Word w)
  deriving DecidableEq

variable {w : ℕ} {C : Type*}

/-- Add an earlier event to the front of a call report. -/
def Report.prepend (e : Event w) (r : Report w) : Report w := ⟨e :: r.events, r.result⟩

/-- Set the addressed external word to the supplied value and preserve all other addresses. -/
def writeMemory (m : Memory w) (a v : Word w) : Memory w :=
  fun i => if i = a.val then v else m i

/-- Apply one event to external memory, storing the supplied value on a write and preserving
memory for every other event. -/
def update (m : Memory w) : Event w → Memory w
  | .write a v => writeMemory m a v
  | _ => m

/-- External memory after applying the writes in a chronological list of events. -/
def after (m : Memory w) (events : List (Event w)) : Memory w := events.foldl update m

/-- Every reported read equals the external word at its address after all preceding writes in
the trace. -/
def Correct (m : Memory w) (events : List (Event w)) : Prop :=
  match events with
  | [] => True
  | .read a v :: es => v = m a.val ∧ Correct m es
  | e :: es => Correct (update m e) es

/-- Extract the binary branch outcomes in order from a call's event trace. -/
def choiceBits : List (Event w) → List Bool
  | [] => []
  | .choice b :: es => b :: choiceBits es
  | _ :: es => choiceBits es

/-- Native execution. Unused choice bits, a rejecting halt, and exhausted
instruction fuel all reject. The exact-use convention gives a unique encoding
of each branch path. -/
def execute (P : Program w C) : ℕ → C → Memory w → List Bool → Option (Report w)
  | 0, _, _, _ => none
  | f + 1, c, m, bits =>
    match P.step c with
    | .localStep c' => (execute P f c' m bits).map (Report.prepend .tick)
    | .branch next =>
      match bits with
      | [] => none
      | b :: bs => (execute P f (next b) m bs).map (Report.prepend (.choice b))
    | .read a next =>
      (execute P f (next (m a.val)) m bits).map (Report.prepend (.read a (m a.val)))
    | .write a v c' =>
      (execute P f c' (writeMemory m a v) bits).map (Report.prepend (.write a v))
    | .finish r => if bits = [] then some ⟨[], r⟩ else none
    | .reject => none

/-- Local call execution. Each external read guesses an arbitrary word. -/
inductive Guessed (P : Program w C) : ℕ → C → List (Event w) → Option (Word w) → Prop
  | done {f c r} (h : P.step c = .finish r) : Guessed P (f + 1) c [] r
  | step {f c c' es r} (h : P.step c = .localStep c') (tail : Guessed P f c' es r) :
      Guessed P (f + 1) c (.tick :: es) r
  | branch {f c next b es r} (h : P.step c = .branch next) (tail : Guessed P f (next b) es r) :
      Guessed P (f + 1) c (.choice b :: es) r
  | read {f c a next v es r} (h : P.step c = .read a next) (tail : Guessed P f (next v) es r) :
      Guessed P (f + 1) c (.read a v :: es) r
  | write {f c a v c' es r} (h : P.step c = .write a v c') (tail : Guessed P f c' es r) :
      Guessed P (f + 1) c (.write a v :: es) r

theorem Guessed.to_execute {P : Program w C} {f c es r} (h : Guessed P f c es r)
    {m : Memory w} (hm : Correct m es) :
    execute P f c m (choiceBits es) = some ⟨es, r⟩ := by
  induction h generalizing m with
  | done h => simp [execute, h, choiceBits]
  | step h _ ih =>
    simp only [execute, h, choiceBits, Option.map_eq_some_iff]
    exact ⟨_, ih hm, rfl⟩
  | branch h _ ih =>
    simp only [execute, h, choiceBits, Option.map_eq_some_iff]
    exact ⟨_, ih hm, rfl⟩
  | read h _ ih =>
    obtain ⟨rfl, hc⟩ := hm
    simp [execute, h, choiceBits, ih hc, Report.prepend]
  | write h _ ih =>
    simp only [execute, h, choiceBits, Option.map_eq_some_iff]
    exact ⟨_, ih hm, rfl⟩

theorem execute_spec {P : Program w C} {f c m bits} {r : Report w}
    (h : execute P f c m bits = some r) :
    Guessed P f c r.events r.result ∧ Correct m r.events ∧ choiceBits r.events = bits := by
  induction f generalizing c m bits r with
  | zero => simp [execute] at h
  | succ f ih =>
    cases hs : P.step c with
    | reject => simp [execute, hs] at h
    | finish result =>
      by_cases hb : bits = []
      · subst bits
        simp [execute, hs] at h
        subst r
        exact ⟨.done hs, trivial, rfl⟩
      · simp [execute, hs, hb] at h
    | localStep next =>
      simp only [execute, hs, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, rfl⟩ := h
      obtain ⟨hg, hm, hb⟩ := ih ht
      exact ⟨.step hs hg, hm, hb⟩
    | branch next =>
      cases bits with
      | nil => simp [execute, hs] at h
      | cons b bits =>
        simp only [execute, hs, Option.map_eq_some_iff] at h
        obtain ⟨t, ht, rfl⟩ := h
        obtain ⟨hg, hm, hb⟩ := ih ht
        exact ⟨.branch hs hg, hm, congrArg (b :: ·) hb⟩
    | read a next =>
      simp only [execute, hs, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, rfl⟩ := h
      obtain ⟨hg, hm, hb⟩ := ih ht
      exact ⟨.read hs hg, ⟨rfl, hm⟩, hb⟩
    | write a v next =>
      simp only [execute, hs, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, rfl⟩ := h
      obtain ⟨hg, hm, hb⟩ := ih ht
      exact ⟨.write hs hg, hm, hb⟩

/-- Correct read guesses leave one transcript per path of binary choices. -/
theorem execute_iff {P : Program w C} {f c m bits} {r : Report w} :
    execute P f c m bits = some r ↔
      Guessed P f c r.events r.result ∧ Correct m r.events ∧ choiceBits r.events = bits := by
  refine ⟨execute_spec, ?_⟩
  rintro ⟨hg, hm, rfl⟩
  exact hg.to_execute hm

theorem Guessed.length_lt {P : Program w C} {f c es r} (h : Guessed P f c es r) :
    es.length < f := by
  induction h <;> simp_all

end BurstRAM

end VPVNP
end Computability
end OAI
