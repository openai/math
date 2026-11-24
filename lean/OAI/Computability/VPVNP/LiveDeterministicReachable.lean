import OAI.Computability.VPVNP.LiveHeaderUnique

/-!
# Address preservation on every continuing native history

A continuing history records every successful call which returned a cursor.
It may have no accepting extension. A verified prefix of empty-choice calls
can be removed when proving address preservation: the first report of each
such call is forced, and every continuing history beyond the prefix starts
from its actual cursor and memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C : Type*}

/-- All states and memories reached through a finite number of continuing calls. -/
inductive Reached (P : Program w C) (fuel : ℕ) (st : Word w) (m : Memory w) : Word w → Memory w → Prop
  | start : Reached P fuel st m st m
  | more {cursor mem bits r next} : Reached P fuel st m cursor mem →
      execute P fuel (P.start cursor) mem bits = some r → r.result = some next →
      Reached P fuel st m next (after mem r.events)

/-- Every returning call leaves this address unchanged, even on a history
whose subsequent calls may reject. -/
def ProtectsAddress (P : Program w C) (fuel : ℕ) (st : Word w) (m : Memory w) (a : ℕ) : Prop :=
  ∀ {cursor mem bits r next}, Reached P fuel st m cursor mem →
    execute P fuel (P.start cursor) mem bits = some r → r.result = some next →
    after mem r.events a = mem a

variable {P : Program w C} {fuel : ℕ} {st : Word w} {m : Memory w} {a : ℕ}

/-- A state and memory invariant can establish the address frame on all
continuing histories by one-call induction. -/
theorem ProtectsAddress.of_invariant (I : Word w → Memory w → Prop) (start : I st m)
    (step : ∀ {cursor mem bits r next}, I cursor mem → execute P fuel (P.start cursor) mem bits = some r →
      r.result = some next → I next (after mem r.events) ∧ after mem r.events a = mem a) :
    ProtectsAddress P fuel st m a := by
  have inv : ∀ {cursor mem}, Reached P fuel st m cursor mem → I cursor mem := by
    intro cursor mem reached
    induction reached with
    | start => exact start
    | more _ call cont ih => exact (step ih call cont).1
  intro cursor mem bits r next reached run result
  exact (step (inv reached) run result).2

private theorem protects_after_empty_call {r : Report w} {next : Word w}
    (run : execute P fuel (P.start st) m [] = some r) (result : r.result = some next)
    (frame : after m r.events a = m a) (suffix : ProtectsAddress P fuel next (after m r.events) a) :
    ProtectsAddress P fuel st m a := by
  let I := fun cursor mem => (cursor = st ∧ mem = m) ∨ Reached P fuel next (after m r.events) cursor mem
  apply ProtectsAddress.of_invariant I (Or.inl ⟨rfl,rfl⟩)
  intro cursor mem bits q v inv call cont
  rcases inv with ⟨rfl,rfl⟩ | reached
  · obtain ⟨_,rfl⟩ := execute_empty_forces run call
    have hv : v = next := Option.some.inj (cont.symm.trans result)
    subst v
    exact ⟨Or.inr .start,frame⟩
  · exact ⟨Or.inr (.more reached call cont),suffix reached call cont⟩

/-- Replay each report on its actual input memory, preserving the protected address. -/
def ReplayFrame (a : ℕ) : Memory w → List (Report w) → Prop
  | _, [] => True
  | m, r :: rs => after m r.events a = m a ∧ ReplayFrame a (after m r.events) rs

/-- The memory reached after the full replay retains the protected cell. -/
theorem ReplayFrame.after_eventLog (rs : List (Report w)) (m : Memory w) (h : ReplayFrame a m rs) :
    after m (eventLog rs) a = m a := by
  induction rs generalizing m with
  | nil => rfl
  | cons r rs ih =>
    change after m (r.events ++ eventLog rs) a = m a
    rw [show after m (r.events ++ eventLog rs) = after (after m r.events) (eventLog rs) from List.foldl_append]
    exact (ih _ h.2).trans h.1

/-- An indexed sequence of actual intermediate memories supplies the frame
for every report along its replay. -/
theorem ReplayFrame.ofFn {n : ℕ} (entry : Fin (n+1) → Memory w) (rs : Fin n → Report w)
    (step : ∀ i : Fin n, after (entry i.castSucc) (rs i).events = entry i.succ)
    (frame : ∀ i : Fin n, entry i.succ a = entry i.castSucc a) : ReplayFrame a (entry 0) (List.ofFn rs) := by
  induction n with
  | zero => simp [ReplayFrame]
  | succ n ih =>
    rw [List.ofFn_succ]
    constructor
    · exact (congrFun (step 0) a).trans (frame 0)
    · rw [show after (entry 0) (rs 0).events = entry (Fin.succ 0) from step 0]
      exact ih (fun i => entry i.succ) (Fin.tail rs) (fun i => step i.succ) (fun i => frame i.succ)

/-- A deterministic startup with address-preserving reports can precede any
address-preserving suffix. The post-startup memory is obtained by replaying
its complete event log, and its persistent word is the reported final cursor. -/
theorem protects_after_replayed_prefix {n : ℕ} {logs : List (Report w)} {next : Word w}
    (run : runSegment P fuel (some st) m (List.replicate n []) = some logs)
    (finish : endState (some st) logs = some next)
    (frame : ReplayFrame a m logs)
    (suffix : ProtectsAddress P fuel next (after m (eventLog logs)) a) : ProtectsAddress P fuel st m a := by
  induction n generalizing st m logs with
  | zero =>
    simp only [List.replicate_zero,runSegment,Option.some.injEq] at run
    subst logs
    change some st = some next at finish
    exact Option.some.inj finish ▸ suffix
  | succ n ih =>
    rw [List.replicate_succ,runSegment] at run
    cases call : execute P fuel (P.start st) m [] with
    | none => simp [call] at run
    | some r =>
      simp only [call,Option.map_eq_some_iff] at run
      obtain ⟨rest,run,rfl⟩ := run
      change endState r.result rest = some next at finish
      have tail : ProtectsAddress P fuel next (after (after m r.events) (eventLog rest)) a := by
        rw [show after (after m r.events) (eventLog rest) = after m (eventLog (r::rest)) by
          simp only [eventLog,List.flatMap_cons,after,List.foldl_append]]
        exact @suffix
      cases cont : r.result with
      | none =>
        rw [cont] at run finish
        cases n with
        | zero => simp [runSegment] at run; subst rest; contradiction
        | succ n => simp [List.replicate_succ,runSegment] at run
      | some cursor =>
        rw [cont] at run finish
        apply protects_after_empty_call call cont frame.1
        apply ih run finish frame.2
        exact @tail

/-- The uniform memory frame implies the frame on the actual prefix. -/
theorem protects_after_empty_prefix {n : ℕ} {logs : List (Report w)} {next : Word w}
    (run : runSegment P fuel (some st) m (List.replicate n []) = some logs)
    (finish : endState (some st) logs = some next)
    (frame : ∀ r ∈ logs, ∀ mem, after mem r.events a = mem a)
    (suffix : ProtectsAddress P fuel next (after m (eventLog logs)) a) : ProtectsAddress P fuel st m a := by
  have lift (es : List (Report w)) (mem : Memory w)
      (keep : ∀ r ∈ es, ∀ m', after m' r.events a = m' a) : ReplayFrame a mem es := by
    induction es generalizing mem with
    | nil => trivial
    | cons r rs ih => exact ⟨keep r (by simp) mem, ih _ (fun q hq => keep q (List.mem_cons_of_mem _ hq))⟩
  apply protects_after_replayed_prefix run finish (lift logs m frame)
  exact @suffix

end BurstRAM

end VPVNP
end Computability
end OAI
