import OAI.Computability.VPVNP.LiveCompressedPairProtection

/-! # All reachable terminal reports preserve a selected cell

The forced empty-choice prefix uses its chronological input memories. The
subsequent calls may halt or continue. Both outcomes preserve the word
whenever their actual reachable source table preserves it.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C : Type*}

/-- A frame for every successful call, including the final accepting call. -/
def PreservesCell (P : Program w C) (fuel : ℕ) (st : Word w) (m : Memory w) (a : ℕ) : Prop :=
  ∀ {cursor mem bits r}, Reached P fuel st m cursor mem →
    execute P fuel (P.start cursor) mem bits = some r → after mem r.events a = mem a

variable {P : Program w C} {fuel : ℕ} {st : Word w} {m : Memory w} {a : ℕ}

/-- Each reachable boundary is either the starting one or a boundary in
the suffix of the forced call. -/
private theorem reached_after_empty_call {r : Report w} {next : Word w}
    (run : execute P fuel (P.start st) m [] = some r) (result : r.result = some next)
    {cursor mem} (reached : Reached P fuel st m cursor mem) :
    (cursor = st ∧ mem = m) ∨ Reached P fuel next (after m r.events) cursor mem := by
  induction reached with
  | start => exact Or.inl ⟨rfl,rfl⟩
  | @more cur now bits rep stop prior call cont ih =>
    rcases ih with ⟨rfl,rfl⟩ | suffix
    · obtain ⟨_,rfl⟩ := execute_empty_forces run call
      have eqn : stop = next := Option.some.inj (cont.symm.trans result)
      subst stop
      exact Or.inr .start
    · exact Or.inr (.more suffix call cont)

private theorem preservesCell_after_empty_call {r : Report w} {next : Word w}
    (run : execute P fuel (P.start st) m [] = some r) (result : r.result = some next)
    (frame : after m r.events a = m a) (suffix : PreservesCell P fuel next (after m r.events) a) :
    PreservesCell P fuel st m a := by
  intro cursor mem bits q reached call
  rcases reached_after_empty_call run result reached with ⟨rfl,rfl⟩ | past
  · obtain ⟨_,rfl⟩ := execute_empty_forces run call
    exact frame
  · exact suffix past call

/-- Replay the deterministic reports on their actual incoming memories, then
apply the suffix's frame to every successful call, including a halting one. -/
theorem preservesCell_after_replayed_prefix {n : ℕ} {logs : List (Report w)} {next : Word w}
    (run : runSegment P fuel (some st) m (List.replicate n []) = some logs)
    (finish : endState (some st) logs = some next)
    (frame : ReplayFrame a m logs)
    (suffix : PreservesCell P fuel next (after m (eventLog logs)) a) : PreservesCell P fuel st m a := by
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
      have tail : PreservesCell P fuel next (after (after m r.events) (eventLog rest)) a := by
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
        apply preservesCell_after_empty_call call cont frame.1
        apply ih run finish frame.2
        exact @tail

end BurstRAM

namespace LiveProgram.CompressedPair

open BurstRAM CompressorRecords CompressorRecords.Schedule LiveStageLink
variable {w d initial phases : ℕ} {C : Catalog d} {b : Bootstrap} {plan : Online.Config C initial phases}
  {last : PairTable} {pub : Fin 11 → Word w} {clock : ℕ} {s : Stage} {m : Memory w}

/-- A physically reachable pair source has the same continuing history
in the ordinary burst RAM semantics. -/
theorem SourceReachable.reached {st : Word w} {mem : Memory w}
    (h : SourceReachable b plan last pub clock s m st mem) :
    Reached (original b plan last pub s) (clockAt pub clock s) 0 m st mem := by
  induction h with
  | start => exact .start
  | more _ call cont ih => exact .more ih call cont

/-- Use a full reachable frame on the source's tag to establish the pair
linker's invariant, even when a partial computation cannot be extended. -/
def Protected.ofPreservesCell
    (tag : PreservesCell (original b plan last pub s) (clockAt pub clock s) 0 m (PairTag.address pub).val) :
    Protected b plan last pub clock s m :=
  Protected.ofSource b plan last pub clock s m (fun reach _ call _ => tag reach.reached call)

theorem Protected.ofPreservesCell_word
    (tag : PreservesCell (original b plan last pub s) (clockAt pub clock s) 0 m (PairTag.address pub).val)
    {a : ℕ} (cell : PreservesCell (original b plan last pub s) (clockAt pub clock s) 0 m a) :
    (Protected.ofPreservesCell tag).word a :=
  Protected.ofSource_word b plan last pub clock s m a
    (fun reach _ call _ => tag reach.reached call) (fun reach _ call => cell reach.reached call)

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
