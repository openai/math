import OAI.Computability.VPVNP.PairSimulationStackCalls
import OAI.Computability.VPVNP.PairSimulationStackSteps
import OAI.Computability.VPVNP.PrimedInputRAMFlowEval
import OAI.Computability.VPVNP.RAMTapeSpace
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Running a virtual stack call inside the native pair simulation

The private RAM rows consume exactly the source branch prefix, ending with
the same stack bank. The caller may use every bit left over. Closing the call
with an accepting continuation recovers exactly the bounded stack path count,
including coincident successors of a choice.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.StackMachine

open RAMTape BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open StackCompiler (Reach)

variable {K Q : Type} [DecidableEq K] {w p r k : ℕ}
  {M : Machine w p r k} {code : StackCode K Q} {pc : Q → Fin 7 → Fin p}
  {reg : Register K ↪ Fin r} {done : Fin p} {L : Layout K w}

/-- The exact native prefix of an accepted call and the interpreter's
behavior on every other stream. Each continuing stack row costs four
native instructions and a true halt costs one. Thus three instructions
from the final row are available to its continuation. -/
def NativeCall (M : Machine w p r k) (L : Layout K w) (reg : Register K ↪ Fin r)
    (done : Fin p) (extra clock : ℕ) (c : Config w p r) (m : Memory w) (bits : List Bool)
    (result : Option (Exit K Q)) : Prop :=
  match result with
  | some x =>
    if x.accept then ∃ es out, Prefix M c es out ∧ out.pc = done ∧
      Represents L reg out x.bank ∧ Frame L reg c out ∧
      bits = choiceBits es ++ x.rest ∧ es.length + 4 * x.unused + 3 = clock
    else execute M.program (extra + clock) c m bits = none
  | none => execute M.program (extra + clock) c m bits = none

omit [DecidableEq K] in
private theorem prepend {c d : Config w p r} {es : List (Event w)}
    {extra clock : ℕ} {m : Memory w} {bits : List Bool} {res : Option (Exit K Q)}
    (pref : Prefix M c es d) (frame : Frame L reg c d)
    (tail : NativeCall M L reg done extra clock d m bits res) :
    NativeCall M L reg done extra (clock + es.length) c m (choiceBits es ++ bits) res := by
  cases res with
  | none =>
    change execute M.program (extra + (clock + es.length)) c m _ = none
    rw [← Nat.add_assoc, pref.execute, tail]
    rfl
  | some x =>
    by_cases hx : x.accept = true <;> simp only [NativeCall, hx, ↓reduceIte] at tail ⊢
    · obtain ⟨fs, out, run, hout, rep, fr, hbits, time⟩ := tail
      refine ⟨es ++ fs, out, pref.append run, hout, rep, frame.trans fr, ?_, ?_⟩
      · simp only [PrimedInputRAM.Flow.choiceBits_append, List.append_assoc, hbits]
      · rw [List.length_append]
        omega
    · rw [← Nat.add_assoc, pref.execute, tail]
      rfl

private theorem parse_native_from {start q : Q} {initial s : Stacks K}
    (linked : Linked M code pc reg done) (hw : 0 < w)
    (space : ∀ ⦃v u⦄, Reach code start initial v u → ∀ j, (u j).length ≤ L.capacity)
    (reach : Reach code start initial q s) (fuel extra : ℕ)
    (cutoff : extra = 0 ∨ StopsWithin code fuel q s)
    (c : Config w p r) (atPC : c.pc = pc q 0) (rep : Represents L reg c s)
    (m : Memory w) (bits : List Bool) :
    NativeCall M L reg done extra (4 * fuel) c m bits (parse code fuel q s bits) := by
  induction fuel generalizing q s c bits with
  | zero =>
    obtain rfl := cutoff.resolve_right (by simp [StopsWithin])
    rfl
  | succ fuel ih =>
    have cont {next : Q} {out : Stacks K} {d : Config w p r} {es : List (Event w)}
        {more : List Bool} (reached : Reach code start initial next out)
        (cuts : extra = 0 ∨ StopsWithin code fuel next out)
        (step : Prefix M c es d) (label : d.pc = pc next 0) (hr : Represents L reg d out)
        (fr : Frame L reg c d) (used : bits = choiceBits es ++ more) (ticks : es.length = 4) :
        NativeCall M L reg done extra (4 * (fuel + 1)) c m bits (parse code fuel next out more) := by
      simpa only [Nat.mul_succ, ← used, ticks] using
        prepend step fr (ih reached cuts d label hr more)
    cases hop : code q with
    | push a b next =>
      have reached := reach.step (.push hop)
      have capacity := space reached a
      simp only [Function.update_self, List.length_cons] at capacity
      obtain ⟨d, run, label, hr, frame⟩ :=
        push_prefix linked hop atPC rep (space reach) (by omega)
      simp only [parse, hop]
      exact cont reached (cutoff.imp_right fun h => by simpa only [StopsWithin, hop] using h)
        run label hr frame rfl rfl
    | pop a next =>
      obtain ⟨d, run, label, hr, frame⟩ := pop_prefix linked hop atPC rep hw (space reach a)
      simp only [parse, hop]
      exact cont (reach.step (.pop hop)) (cutoff.imp_right fun h => by simpa only [StopsWithin, hop] using h)
        run label hr frame rfl rfl
    | goto next =>
      obtain ⟨d, run, label, hr, frame⟩ := goto_prefix linked hop atPC rep
      simp only [parse, hop]
      exact cont (reach.step (.goto hop)) (cutoff.imp_right fun h => by simpa only [StopsWithin, hop] using h)
        run label hr frame rfl rfl
    | choose low high =>
      cases bits with
      | nil =>
        simp only [parse, hop, NativeCall]
        obtain ⟨_, run, _⟩ := choose_prefix linked hop atPC rep false
        exact run.execute_short _ m [] [] false rfl
      | cons b more =>
        obtain ⟨d, run, label, hr, frame⟩ := choose_prefix linked hop atPC rep b
        have reached : Reach code start initial (if b then high else low) s := by
          cases b with
          | false => exact .low reach hop
          | true => exact .high reach hop
        have cuts := cutoff.imp_right fun h => by
          simp only [StopsWithin, hop] at h
          exact (show StopsWithin code fuel (if b then high else low) s from
            by cases b <;> first | exact h.1 | exact h.2)
        simp only [parse, hop]
        exact cont reached cuts run label hr frame rfl rfl
    | halt b =>
      cases b with
      | false =>
        simp only [parse, hop, NativeCall, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.mul_succ, show extra + (4 * fuel + 4) = (extra + 4 * fuel + 3) + 1 by omega]
        simp [execute, halt_reject linked hop atPC]
      | true =>
        obtain ⟨d, run, label, hr, frame⟩ := halt_prefix linked hop atPC rep
        simp only [parse, hop, NativeCall, ↓reduceIte]
        exact ⟨_, d, run, label, hr, frame, rfl, by simp [Nat.mul_succ]; omega⟩

/-- A bounded source run needs at most one additional cell per source
instruction on each stack. This gives an interval size when a separate
space estimate is unavailable. -/
theorem reachable_capacity {q : Q} {s : Stacks K} {fuel cap : ℕ}
    (halt : StopsWithin code fuel q s) (fit : ∀ j, (s j).length + fuel ≤ cap)
    {v : Q} {u : Stacks K} (path : Reach code q s v u) (j : K) :
    (u j).length ≤ cap := by
  have carries : ∃ t, StopsWithin code t v u ∧ ∀ i, (u i).length + t ≤ cap := by
    induction path with
    | initial => exact ⟨fuel, halt, fit⟩
    | step _ move ih =>
      obtain ⟨t, stops, room⟩ := ih
      cases t with
      | zero => exact stops.elim
      | succ t =>
        cases move with
        | push h =>
          refine ⟨t, by simpa only [StopsWithin, h] using stops, fun i => ?_⟩
          have hi := room i
          rw [Function.update_apply]
          split_ifs with e
          · subst i; simp only [List.length_cons]; omega
          · omega
        | pop h =>
          refine ⟨t, by simpa only [StopsWithin, h] using stops, fun i => ?_⟩
          have hi := room i
          rw [Function.update_apply]
          split_ifs with e
          · subst i; simp only [List.length_tail]; omega
          · omega
        | goto h =>
          refine ⟨t, by simpa only [StopsWithin, h] using stops, fun i => ?_⟩
          have := room i
          omega
    | low _ h ih | high _ h ih =>
      obtain ⟨t, stops, room⟩ := ih
      cases t with
      | zero => exact stops.elim
      | succ t =>
        simp only [StopsWithin, h] at stops
        refine ⟨t, ?_, fun i => (Nat.le_add_right _ 1).trans (room i)⟩
        first | exact stops.1 | exact stops.2
  obtain ⟨t, _, room⟩ := carries
  exact (Nat.le_add_right _ _).trans (room j)

/-- Every branch of the private RAM stack fragment agrees with the source
interpreter. At the exact native cutoff no source termination premise is
needed. A source stopping bound also permits arbitrary extra native fuel. -/
theorem parse_native {q : Q} {s : Stacks K} (linked : Linked M code pc reg done) (hw : 0 < w)
    (space : ∀ ⦃v u⦄, Reach code q s v u → ∀ j, (u j).length ≤ L.capacity)
    (fuel extra : ℕ) (cutoff : extra = 0 ∨ StopsWithin code fuel q s)
    (c : Config w p r) (atPC : c.pc = pc q 0) (rep : Represents L reg c s)
    (m : Memory w) (bits : List Bool) :
    NativeCall M L reg done extra (4 * fuel) c m bits (parse code fuel q s bits) :=
  parse_native_from linked hw space .initial fuel extra cutoff c atPC rep m bits

/-- For a true source halt, the caller resumes from the actual native
configuration, with arbitrary continuation fuel and the entire unused suffix. -/
theorem execute_continuation {q : Q} {s : Stacks K} (linked : Linked M code pc reg done)
    (hw : 0 < w) (space : ∀ ⦃v u⦄, Reach code q s v u → ∀ j, (u j).length ≤ L.capacity)
    {fuel : ℕ} {bits : List Bool} {x : Exit K Q} (accepted : parse code fuel q s bits = some x)
    (ok : x.accept = true) (c : Config w p r) (atPC : c.pc = pc q 0) (rep : Represents L reg c s)
    (m : Memory w) :
    ∃ es out, out.pc = done ∧ Represents L reg out x.bank ∧ Frame L reg c out ∧
      bits = choiceBits es ++ x.rest ∧ es.length + 4 * x.unused + 3 = 4 * fuel ∧
      ∀ t, execute M.program (t + es.length) c m bits =
        (execute M.program t out m x.rest).map (fun r => ⟨es ++ r.events, r.result⟩) := by
  have h := parse_native linked hw space fuel 0 (.inl rfl) c atPC rep m bits
  simp only [accepted, NativeCall, ok, ↓reduceIte] at h
  obtain ⟨es, out, pref, label, hr, frame, used, time⟩ := h
  exact ⟨es, out, label, hr, frame, used, time, fun t => by rw [used]; exact pref.execute t m x.rest⟩

/-- Closing with the native accept instruction consumes exactly one of
the complete successful source words. This holds even with coincident
choice successors and early halts. -/
theorem execute_accept_iff {q : Q} {s : Stacks K} (linked : Linked M code pc reg done)
    (close : M.code done = .accept) (hw : 0 < w)
    (space : ∀ ⦃v u⦄, Reach code q s v u → ∀ j, (u j).length ≤ L.capacity)
    (fuel extra : ℕ) (cutoff : extra = 0 ∨ StopsWithin code fuel q s)
    (c : Config w p r) (atPC : c.pc = pc q 0) (rep : Represents L reg c s)
    (m : Memory w) (bits : List Bool) :
    (execute M.program (extra + 4 * fuel) c m bits).isSome = true ↔
      acceptPrefix code fuel q s bits = some [] := by
  have call := parse_native linked hw space fuel extra cutoff c atPC rep m bits
  cases hx : parse code fuel q s bits with
  | none =>
    simp only [hx, NativeCall] at call
    simp [call, acceptPrefix, haltPrefix, hx]
  | some x =>
    cases ok : x.accept with
    | false =>
      simp only [hx, NativeCall, ok, Bool.false_eq_true, ↓reduceIte] at call
      simp [call, acceptPrefix, haltPrefix, hx, ok]
    | true =>
      simp only [hx, NativeCall, ok, ↓reduceIte] at call
      obtain ⟨es, out, pref, label, _, _, used, time⟩ := call
      have step : M.program.step out = .finish none := by simp [Machine.program, label, close, Instr.run]
      simp only [acceptPrefix, haltPrefix, hx, ok, ↓reduceIte, Option.some.injEq]
      rw [show extra + 4 * fuel = (extra + 4 * x.unused + 2 + 1) + es.length by omega,
        used, pref.execute, execute, step]
      by_cases hrest : x.rest = [] <;> simp [hrest]

/-- The native private RAM call has the same multiplicity as the capped
stack machine. All initial banks obeying the representation and every
external memory give the same equality. -/
theorem nativeStreams_card {q : Q} {s : Stacks K} (linked : Linked M code pc reg done)
    (close : M.code done = .accept) (hw : 0 < w)
    (space : ∀ ⦃v u⦄, Reach code q s v u → ∀ j, (u j).length ≤ L.capacity)
    (fuel extra : ℕ) (cutoff : extra = 0 ∨ StopsWithin code fuel q s)
    (c : Config w p r) (atPC : c.pc = pc q 0) (rep : Represents L reg c s) (m : Memory w) :
    Nat.card {bs : List Bool // (execute M.program (extra + 4 * fuel) c m bs).isSome = true} =
      stackPaths code fuel q s := by
  let same : {bs : List Bool // (execute M.program (extra + 4 * fuel) c m bs).isSome = true} ≃
      CompleteStreams code fuel q s := Equiv.subtypeEquivRight fun bs =>
    execute_accept_iff linked close hw space fuel extra cutoff c atPC rep m bs
  rw [Nat.card_congr same, Nat.card_eq_fintype_card, completeStreams_card]

end PairSimulation.StackMachine

end VPVNP
end Computability
end OAI
