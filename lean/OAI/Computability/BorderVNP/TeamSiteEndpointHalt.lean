import OAI.Computability.BorderVNP.TeamSiteEndpointRuns

/-!
# Propagating an already accepted processor through its physical endpoint

The predecessor decoder installs the canonical halt, checks its elapsed time
and bypasses the signed instruction loop. The final processor accepts with
positive sign. An interior processor writes the canonical halted frame and
compares it with the outgoing candidate. Neither path consumes choice bits
or touches the record buffer.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Endpoint

open VPVNP RAMTape BurstRAM TeamLocalClock TeamTapeHandoff TeamPrivateFragment

variable {w p r k a m g d : ℕ} {Q Γ : Type}

/-- Acceptance of a propagated halt, including the global clock check. The last processor
has no successor link to test. -/
def haltValid (last : Bool) (r : ℕ) (elapsed limit : Word w) (candidate : List Bool) : Bool :=
  decide (elapsed ≤ limit ∧ (last = true ∨ (Frame.accepted elapsed : Frame w r).bits = candidate))

/-- The final in-budget halt has signed value +1 for every outgoing candidate. -/
theorem final_halt_weight (P : TeamOpcode.Program p r k a) (elapsed limit : Word w)
    (safe : elapsed ≤ limit) (candidate : List Bool) :
    weight (finishLabel (P := P) (Q := Q) (m := m) (g := g) (some false)
      (haltValid true r elapsed limit candidate)) = 1 := by
  simp only [haltValid, safe, true_or, and_self, decide_true, weight_finishLabel, ite_true]
  rfl

private theorem decoded_site (pub : Fin k → Word w) (pc : Fin p) (H limit elapsed max : Word w)
    (suffix : List Bool) (base : Stacks (Port r k d)) (u : TeamSite.Port r k d) :
    let core := TeamLocalClock.bank pub ⟨pc, fun _ => 0⟩ H limit elapsed max
    let mid := installStacks startup base
      (Startup.decoded pub (.accepted elapsed) H limit max suffix)
    mid (.site u) = match u with
      | .clock j => core j
      | _ => base (.site u) := by
  intro core mid
  cases u with
  | clock j =>
    have h := installStacks_at startup_injective base
      (Startup.decoded pub (.accepted elapsed) H limit max suffix) (.clock j)
    cases j <;> exact h
  | _ =>
    apply installStacks_outside
    intro j
    cases j <;> simp [startup]

/-- Complete installed path for an already accepted predecessor on an arbitrary processor.
An excessive elapsed time rejects immediately. Otherwise the final processor returns +1,
and an interior processor returns +1 exactly for the identical successor frame. The incident
suffix, all record-buffer stacks and all other non-clock site ports retain their contents. -/
theorem halted_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (last : Bool) (entryPC : Fin p) (fits : p ≤ 2 ^ w) (pub : Fin k → Word w)
    (H limit elapsed max : Word w) (suffix bits : List Bool) (base : Stacks (Port r k (m * g)))
    (ready : base ∘ startup = Startup.input pub H limit max
      ((Frame.accepted elapsed : Frame w r).bits ++ suffix)) (payload : base .payload = []) :
    ∃ t ≤ Startup.budget r w + (7 * r + 45) * (w + 1), ∃ out,
      StackRuns (replay (code P lib)) t (.startup last (Startup.entry p r), bits) base
        (finishLabel (some false) (haltValid last r elapsed limit (base .outgoing)), bits) out ∧
      out .incoming = suffix ∧ ∀ u, out (.site u) = match u with
        | .clock j => TeamLocalClock.bank pub ⟨entryPC, fun _ => 0⟩ H limit elapsed max j
        | _ => base (.site u) := by
  let f : Frame w r := .accepted elapsed
  let decoded := Startup.decoded pub f H limit max suffix
  let mid := installStacks startup base decoded
  let st : TeamOpcode.State w p r := ⟨entryPC, fun _ => 0⟩
  let core := TeamLocalClock.bank pub st H limit elapsed max
  obtain ⟨t, ht, pre⟩ := predecessor_run P lib last fits pub f H limit max suffix bits base ready
  change StackRuns (replay (code P lib)) t (.startup last (Startup.entry p r), bits) base
    (afterStartup last (if elapsed ≤ limit then .accepted else .reject), bits) mid at pre
  have inc : mid .incoming = suffix := installStacks_at startup_injective base decoded .wire
  have sites := decoded_site pub entryPC H limit elapsed max suffix base
  by_cases safe : elapsed ≤ limit
  · rw [ite_eq_left safe] at pre
    have raw : mid .outgoing = base .outgoing :=
      installStacks_outside base decoded (fun u => by cases u <;> simp [startup])
    have readyFinish : mid ∘ finish = Finish.bank core [] (base .outgoing) := by
      funext u
      cases u with
      | clock j => exact sites (.clock j)
      | candidate => exact raw
      | tmp => exact installStacks_at startup_injective base decoded .tmp
      | payload =>
        exact (installStacks_outside (l := Port.payload) base decoded
          (fun u => by cases u <;> simp [startup])).trans payload
    cases last with
    | true =>
      have fin := finish_run P lib (some false) (Finish.last_run (.accepted : Finish.Mode p)
        (Finish.bank core [] (base .outgoing))) mid readyFinish bits
      rw [installStacks_eq finish_injective mid _ (congrFun readyFinish)] at fin
      refine ⟨t + 2, ?_, mid, ?_, inc, fun u => by cases u <;> exact sites _⟩
      · nlinarith [Nat.zero_le (r * w)]
      · simpa only [haltValid, safe, true_or, and_self, decide_true, Finish.Mode.halted]
          using pre.trans fin
    | false =>
      obtain ⟨next, finishRun, preserved⟩ :=
        Finish.successor_run .accepted pub st.logged H limit elapsed max [] (base .outgoing)
      have fin := finish_run P lib (some false) finishRun mid readyFinish bits
      let out := installStacks finish mid next
      let cost := 2 * (8 * w + 3) + (r + 2) * (5 * w + 2) + 2 +
        (2 * min (1 + (r + 2) * w) (base .outgoing).length + 2) + 1 + 1
      refine ⟨t + cost, ?_, out, ?_, ?_, ?_⟩
      · have hmin := min_le_left (1 + (r + 2) * w) (base .outgoing).length
        dsimp only [cost]
        nlinarith [Nat.zero_le (r * w)]
      · by_cases he : (Frame.accepted elapsed : Frame w r).bits = base .outgoing <;>
          simpa only [haltValid, safe, Bool.false_eq_true, false_or, true_and, Finish.frame,
            he, decide_true, decide_false, ite_false, ite_true] using pre.trans fin
      · exact (installStacks_outside mid next (fun u => by cases u <;> simp [finish])).trans inc
      · intro u
        cases u with
        | clock j =>
          exact (installStacks_at finish_injective mid next (.clock j)).trans (preserved j)
        | _ =>
          exact (installStacks_outside mid next (fun u => by cases u <;> simp [finish])).trans
            (sites _)
  · rw [ite_eq_right safe] at pre
    refine ⟨t, ?_, mid, ?_, inc, fun u => by cases u <;> exact sites _⟩
    · nlinarith [Nat.zero_le (r * w)]
    · simpa only [haltValid, safe, false_and, decide_false, finishLabel, Bool.false_eq_true,
        ite_false, afterStartup] using pre

end TeamSite.Endpoint

end BorderVNP
end Computability
end OAI
