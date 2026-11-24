import OAI.Computability.VPVNP.RAMProcessorSiteTestsTree
import OAI.Computability.VPVNP.RAMValidatorControl

/-!
# Entry, call dispatch, and final checks for a RAM processor

A running entry must start inside its own half-open cost bucket. A halted
entry is checked only against the global cap. Later calls may cross the bucket
boundary, including when a final cost equals the global cap. The final
comparison distinguishes an absent outgoing edge from a present halted cut.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteTests

open TapeWord BurstRAM

variable {w : ℕ}

/-- Decode the current cut from the cumulative cost and, while running, the persistent state
word. -/
def Snapshot.cut (s : Snapshot w) : Cut w :=
  ⟨(s.words .cost).val, if s.flags .running then some (s.words .state) else none⟩

/-- Decode the optional outgoing cut using the presence and running flags, target cost and
target state. -/
def Snapshot.target (s : Snapshot w) : Option (Cut w) :=
  if s.flags .hasTarget then
    some ⟨(s.words .targetCost).val, if s.flags .targetRunning then some (s.words .targetState) else none⟩
  else none

/-- Check the incoming range and choose the first site action. -/
def entry : Tree :=
  .branch (.compare .lt .cap .cost) (.leaf .reject) <|
    .branch (.flag .running)
      (.branch (.compare .lt .cost .lower) (.leaf .reject)
        (.branch (.compare .lt .cost .boundary) (.leaf .dispatch) (.leaf .reject)))
      (.leaf .finish)

/-- Test the cut produced by the preceding charged call. -/
def iteration : Tree :=
  .branch (.compare .lt .cap .cost) (.leaf .reject) <|
    .branch (.flag .running)
      (.branch (.compare .lt .cost .boundary) (.leaf .dispatch) (.leaf .finish))
      (.leaf .finish)

/-- Exact use of choices and equality with the successor cut, or acceptance
at the terminal site. The state payload of a halt is ignored. -/
def finalCheck : Tree :=
  .branch .emptyChoices
    (.branch (.flag .hasTarget)
      (.branch (.compare .eq .cost .targetCost)
        (.branch (.flag .running)
          (.branch (.flag .targetRunning)
            (.branch (.compare .eq .state .targetState) (.leaf .finish) (.leaf .reject))
            (.leaf .reject))
          (.branch (.flag .targetRunning) (.leaf .reject) (.leaf .finish)))
        (.leaf .reject))
      (.branch (.flag .running) (.leaf .reject) (.leaf .finish)))
    (.leaf .reject)

theorem entry_eval (s : Snapshot w) :
    entry.eval s = if s.cut.cost ≤ (s.words .cap).val ∧
      (s.cut.state.isSome → (s.words .lower).val ≤ s.cut.cost ∧ s.cut.cost < (s.words .boundary).val)
      then if s.cut.state.isSome then .dispatch else .finish else .reject := by
  cases h : s.flags .running <;>
    simp [entry, Tree.eval, Atom.eval, Comparison.Op.eval, Snapshot.cut, h, Fin.lt_def, -Fin.val_fin_lt, -Fin.val_fin_le] <;>
    split_ifs <;> first | rfl | omega

theorem iteration_eval (s : Snapshot w) :
    iteration.eval s = if s.cut.cost ≤ (s.words .cap).val then
      if s.cut.state.isSome && decide (s.cut.cost < (s.words .boundary).val) then .dispatch else .finish
      else .reject := by
  cases h : s.flags .running <;>
    simp [iteration, Tree.eval, Atom.eval, Comparison.Op.eval, Snapshot.cut, h, Fin.lt_def, -Fin.val_fin_lt, -Fin.val_fin_le] <;>
    split_ifs <;> first | rfl | omega

open Classical in
theorem final_eval (s : Snapshot w) :
    finalCheck.eval s = if s.choices = [] ∧
      (match s.target with | some d => d = s.cut | none => s.cut.state = none)
      then .finish else .reject := by
  cases ht : s.flags .hasTarget <;> cases hs : s.flags .running <;> cases hr : s.flags .targetRunning <;>
    simp [finalCheck, Tree.eval, Atom.eval, Comparison.Op.eval, Snapshot.cut, Snapshot.target, ht, hs, hr,
      Fin.ext_iff] <;>
    split_ifs <;> simp_all

/-- A terminal equality test of the physical processor has exactly the
Boolean outcome of the native report checker. -/
theorem final_eq_finishReports (s : Snapshot w) (input : Cut w) (reports : List (Report w))
    (hc : s.cut = input.advance reports) :
    finalCheck.eval s = if (finishReports input s.target reports s.choices).1 then .finish else .reject := by
  rw [final_eval]
  have valid := finishReports_spec input s.target reports s.choices
  rw [← hc] at valid
  cases ho : s.target <;> simp only [ho] at valid ⊢ <;> split_ifs <;> tauto

/-- The dispatch label selects precisely the native call of this site,
including its remaining credit and unused binary choices. -/
theorem runSiteLoop_at_exit {C : Type*} (P : Program w C) (fuel H steps siteLeft : ℕ) (s : Snapshot w) :
    runSiteLoop P fuel H (s.words .boundary).val (s.words .cap).val steps s.cut siteLeft s.choices =
      match iteration.eval s with
      | .reject => none
      | .finish => some ([], s.choices)
      | .dispatch =>
        match steps with
        | 0 => none
        | j+1 => collectCall (runChargedCall P fuel (P.start (s.words .state)) H
            ((s.words .cap).val - s.cut.cost) siteLeft s.choices).output (fun rep rest =>
              runSiteLoop P fuel H (s.words .boundary).val (s.words .cap).val j (s.cut.advance [rep])
                (siteLeft - (1 + rep.probes)) rest) := by
  rw [runSiteLoop, iteration_eval]
  cases hr : s.flags .running <;>
    by_cases hc : (s.words .cost).val ≤ (s.words .cap).val <;>
      by_cases hb : (s.words .cost).val < (s.words .boundary).val <;>
        simp [Snapshot.cut, hr, hc, hb]
  cases steps <;> rfl

/-- The entry fragment rejects an invalid incoming bucket and immediately
finishes on a valid halted cut. Its dispatch label enters the native site loop. -/
theorem runSite_at_exit {C : Type*} (P : Program w C) (fuel S H v : ℕ) (s : Snapshot w)
    (hl : (s.words .lower).val = v*H) (hb : (s.words .boundary).val = (v+1)*H)
    (hc : (s.words .cap).val = S*H) :
    runSite P fuel S H v s.cut s.choices =
      match entry.eval s with
      | .reject => none
      | .finish => some ([], s.choices)
      | .dispatch => runSiteLoop P fuel H ((v+1)*H) (S*H) (2*H-1) s.cut (2*H-1) s.choices := by
  rw [entry_eval, hl, hb, hc, runSite]
  cases hr : s.flags .running <;>
    by_cases hcap : (s.words .cost).val ≤ S*H <;>
      by_cases hrange : v*H ≤ (s.words .cost).val ∧ (s.words .cost).val < (v+1)*H <;>
        simp [Snapshot.cut, hr, hcap, hrange] <;> rw [runSiteLoop] <;> simp [hcap]

private def Atom.bound (a : Atom) (w : ℕ) : ℕ :=
  match a with | .compare .. => 20*w+10 | _ => 3

private def Tree.bound : Tree → ℕ → ℕ
  | .leaf e, _ => e.bits.length
  | .branch a yes no, w => a.bound w + (max (yes.bound w) (no.bound w) + 1)

private theorem ticks_le (t : Tree) (s : Snapshot w) : t.ticks s ≤ t.bound w := by
  induction t with
  | leaf => exact le_rfl
  | branch a y n iy ineg =>
    have ha : a.ticks s ≤ a.bound w := by
      cases a <;> simp only [Atom.ticks, Atom.bound] <;> first | exact le_rfl | split <;> decide
    dsimp only [Tree.ticks, Tree.bound]
    split <;> omega

theorem entry_work (s : Snapshot w) : entry.ticks s ≤ 60*w+39 := by
  apply (ticks_le entry s).trans
  simp [entry, Tree.bound, Atom.bound, Exit.bits]
  omega

theorem iteration_work (s : Snapshot w) : iteration.ticks s ≤ 40*w+28 := by
  apply (ticks_le iteration s).trans
  simp [iteration, Tree.bound, Atom.bound, Exit.bits]
  omega

theorem final_work (s : Snapshot w) : finalCheck.ticks s ≤ 40*w+40 := by
  apply (ticks_le finalCheck s).trans
  simp [finalCheck, Tree.bound, Atom.bound, Exit.bits]
  omega

end RAMTape.SiteTests

end VPVNP
end Computability
end OAI
