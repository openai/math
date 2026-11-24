import OAI.Computability.VPVNP.LiveStageLinkRun

/-!
# Consecutive calls and overhead of the linked program

The component interpreter reads the stage tag at each call boundary, runs its
own instruction table, and updates the shared memory from its report. It agrees
exactly with the linked finite instruction table on every path, including
malformed tags, unused branch bits, and calls after termination.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveStageLink

open BurstRAM BurstRAM.PrivateRAM

variable {d r k w : ℕ} {pcs : Fin d → ℕ}
variable (T : (s : Fin d) → Template (pcs s) r k) (next : Fin d → Option (Fin d))
variable (pub : Fin k → Word w) (addr : Word w)

/-- The full external trace, including the deterministic dispatcher and transfer. -/
def linkedReport (next : Fin d → Option (Fin d)) (addr : Word w) (s : Fin d) (rep : Report w) : Report w :=
  prependLog (dispatchEvents addr s) (exitReport next addr s rep)

private theorem probe_append (es fs : List (Event w)) : countProbes (es ++ fs) = countProbes es + countProbes fs := by
  induction es with
  | nil => simp [countProbes]
  | cons e es ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]

private theorem bits_append (es fs : List (Event w)) : choiceBits (es ++ fs) = choiceBits es ++ choiceBits fs := by
  induction es with
  | nil => simp [choiceBits]
  | cons e es ih => cases e <;> simp [choiceBits, ih]

private theorem ticks (n : ℕ) : countProbes (List.replicate n (.tick : Event w)) = 0 ∧
    choiceBits (List.replicate n (.tick : Event w)) = [] := by
  induction n with
  | zero => simp [countProbes, choiceBits]
  | succ n ih => simpa [List.replicate_succ, countProbes, choiceBits] using ih

private theorem after_ticks (n : ℕ) (m : Memory w) : after m (List.replicate n .tick) = m := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, after, update] using ih

/-- The linker never guesses an additional bit and never merges two paths with
identical computed states but different original branch choices. -/
theorem linkedReport_choiceBits (s : Fin d) (rep : Report w) :
    choiceBits (linkedReport next addr s rep).events = choiceBits rep.events := by
  cases rep with | mk es val =>
    cases val <;> cases h : next s <;>
      simp [linkedReport, prependLog, exitReport, dispatchEvents, transferEvents, h,
        bits_append, choiceBits, (ticks (w := w) _).2]

/-- Each call adds the tag read and at most one transfer write. -/
theorem linkedReport_probes (s : Fin d) (rep : Report w) :
    (linkedReport next addr s rep).probes = rep.probes + 1 +
      if rep.result = none ∧ (next s).isSome then 1 else 0 := by
  cases rep with | mk es val =>
    cases val <;> cases h : next s <;>
      simp [Report.probes, linkedReport, prependLog, exitReport, dispatchEvents, transferEvents, h,
        probe_append, countProbes, (ticks (w := w) _).1] <;> omega

/-- At most `2d+5` extra instruction dispatches per call. The difference
in report lengths equals the difference in total dispatches, since both
computations use one final instruction after their logged events. -/
theorem linkedReport_length_le (s : Fin d) (rep : Report w) :
    (linkedReport next addr s rep).events.length ≤ rep.events.length + 2*d + 5 := by
  cases rep with | mk es val =>
    cases val <;> cases h : next s <;>
      simp [linkedReport, prependLog, exitReport, dispatchEvents, transferEvents, h] <;>
      have := s.isLt <;> omega

/-- The external memory transition is exactly that of the component, followed
by the one tag write when its accepting exit is connected to a further stage. -/
theorem linkedReport_after (s : Fin d) (rep : Report w) (m : Memory w) :
    after m (linkedReport next addr s rep).events = match rep.result, next s with
      | none, some dest => writeMemory (after m rep.events) addr (tagWord w dest)
      | _, _ => after m rep.events := by
  have ha (u v : List (Event w)) : after m (u ++ v) = after (after m u) v := by
    simp [after, List.foldl_append]
  have hprefix : after m (dispatchEvents addr s) = m := by
    simpa [dispatchEvents, after, update] using after_ticks (2 * (s.val + 1)) m
  cases rep with | mk es val =>
    cases val <;> cases h : next s <;>
      simp only [linkedReport, prependLog, exitReport, h, ha, hprefix, transferEvents]
    all_goals rfl

/-- Replay a single call directly in its source component. Fuel remaining after
dispatch is charged for any transfer as well as the original component trace. -/
def stageCall (fuel : ℕ) (st : Word w) (m : Memory w) (bits : List Bool) : Option (Report w) :=
  if h : (m addr.val).val < d then
    let s : Fin d := ⟨(m addr.val).val, h⟩
    let cap := fuel - (dispatchEvents addr s).length
    let M := ((T s).instantiate w pub).program
    (((execute M cap (M.start st) m bits).bind (boundedExit next addr s cap))).map
      (prependLog (dispatchEvents addr s))
  else none

theorem execute_eq_stageCall (hfits : d ≤ 2^w) (fuel : ℕ) (hcap : 2*d+2 ≤ fuel)
    (st : Word w) (m : Memory w) (bits : List Bool) :
    let L := (machine T next pub addr).program
    execute L fuel (L.start st) m bits = stageCall T next pub addr fuel st m bits := by
  dsimp only
  unfold stageCall
  split_ifs with h
  · let s : Fin d := ⟨(m addr.val).val, h⟩
    have htag : m addr.val = tagWord w s := Fin.ext (by simp [s, tagWord])
    have hl : (dispatchEvents addr s).length ≤ fuel := by
      simp [dispatchEvents]; have := s.isLt; omega
    simpa only [Nat.sub_add_cancel hl] using
      execute_linked T next pub addr s hfits st (fuel - (dispatchEvents addr s).length) m htag bits
  · exact execute_invalid T next pub addr hfits st fuel m (Nat.le_of_not_gt h) bits

private theorem guessed_addFuel {C : Type*} {P : Program w C} {f : ℕ} {c : C} {es out}
    (h : Guessed P f c es out) (pad : ℕ) : Guessed P (f + pad) c es out := by
  induction h with
  | done hs => simpa [Nat.succ_add] using Guessed.done (f := _ + pad) hs
  | step hs _ ih => simpa [Nat.succ_add] using Guessed.step hs ih
  | branch hs _ ih => simpa [Nat.succ_add] using Guessed.branch hs ih
  | read hs _ ih => simpa [Nat.succ_add] using Guessed.read hs ih
  | write hs _ ih => simpa [Nat.succ_add] using Guessed.write hs ih

private theorem guessed_length {C : Type*} {P : Program w C} {f : ℕ} {c : C} {es out}
    (h : Guessed P f c es out) : es.length < f := by induction h <;> simp_all

/-- An ordinary successful component call can be used directly at any linked cap
with `2d+5` units of slack. Its exact branch string and computed report are retained. -/
theorem execute_linked_of_stage {f cap : ℕ} (s : Fin d) (hfits : d ≤ 2^w)
    (hcap : f + 2*d + 5 ≤ cap) (st : Word w) (m : Memory w) (htag : m addr.val = tagWord w s)
    (bits : List Bool) (rep : Report w)
    (hcall : execute ((T s).instantiate w pub).program f (((T s).instantiate w pub).program.start st) m bits = some rep) :
    execute (machine T next pub addr).program cap ((machine T next pub addr).program.start st) m bits =
      some (linkedReport next addr s rep) := by
  let startup := (dispatchEvents addr s).length
  have hs : startup ≤ 2*d+2 := by simp [startup, dispatchEvents]; have := s.isLt; omega
  have hf : f ≤ cap - startup := by omega
  obtain ⟨hg, hm, hbits⟩ := execute_spec hcall
  have hr : execute ((T s).instantiate w pub).program (cap-startup)
      (((T s).instantiate w pub).program.start st) m bits = some rep := by
    apply execute_iff.mpr
    refine ⟨?_, hm, hbits⟩
    simpa only [Nat.add_sub_cancel' hf] using guessed_addFuel hg (cap-startup-f)
  have hb : (exitReport next addr s rep).events.length < cap-startup := by
    have hlen := guessed_length hg
    have hroom : f + 3 ≤ cap-startup := by omega
    cases rep with | mk es out =>
      change es.length < f at hlen
      cases out <;> cases he : next s <;> simp [exitReport, transferEvents, he] <;> omega
  have h := execute_linked T next pub addr s hfits st (cap-startup) m htag bits
  simpa only [show cap-startup+(dispatchEvents addr s).length = cap by omega, hr, Option.bind_some,
    boundedExit, ite_eq_left hb, Option.map_some, linkedReport] using h

/-- Path composition of the individual source stages, resetting private data
on every call and using the exact post-state and memory of its predecessor. -/
def stageSegment (fuel : ℕ) : Option (Word w) → Memory w → List (List Bool) → Option (List (Report w))
  | _, _, [] => some []
  | none, _, _ :: _ => none
  | some st, m, bs :: more => do
    let rep ← stageCall T next pub addr fuel st m bs
    let tail ← stageSegment fuel rep.result (after m rep.events) more
    return rep :: tail

/-- The source-stage path composition and the native linked machine accept
precisely the same per-call branch strings and produce identical reports. -/
theorem runSegment_eq_stageSegment (hfits : d ≤ 2^w) (fuel : ℕ) (hcap : 2*d+2 ≤ fuel)
    (st : Option (Word w)) (m : Memory w) (bits : List (List Bool)) :
    runSegment (machine T next pub addr).program fuel st m bits =
      stageSegment T next pub addr fuel st m bits := by
  induction bits generalizing st m with
  | nil => rfl
  | cons bs more ih =>
    cases st with
    | none => rfl
    | some st =>
      rw [runSegment, stageSegment, execute_eq_stageCall T next pub addr hfits fuel hcap]
      cases hs : stageCall T next pub addr fuel st m bs with
      | none => rfl
      | some rep =>
        dsimp only
        rw [ih]
        change (stageSegment T next pub addr fuel rep.result (after m rep.events) more).map (rep :: ·) =
          (stageSegment T next pub addr fuel rep.result (after m rep.events) more).bind (fun tail => some (rep :: tail))
        cases stageSegment T next pub addr fuel rep.result (after m rep.events) more <;> rfl

end LiveStageLink

end VPVNP
end Computability
end OAI
