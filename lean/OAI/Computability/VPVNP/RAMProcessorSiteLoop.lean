import OAI.Computability.VPVNP.RAMProcessorSiteProgress

/-!
# Following the physical loop through all calls of a cost bucket

Every successful start decreases the site allowance. In particular, when
the native call-count bound is exhausted the next attempted start has zero
credit and physically rejects. A failed call retains its actual halting
row even when earlier calls have already returned.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM RAMSerialization

variable {w p r k : ℕ}

/-- Select the first-call label at bucket entry or the new-call label for a later iteration. -/
def startLabel (first : Bool) : Label p r := if first then .first else .newCall

/-- The two startup labels have the same charged call specification.
The first one additionally initializes the global allowance. -/
def StartRuns (T : Template p r k) (ready : Bool → BoundaryInvariant w p r k) (work : ℕ) :=
  ∀ (first : Bool) (s : Snapshot w p r k) (records : List (WordRecord w)), ready first s records →
    SiteTests.iteration.eval s.tests = .dispatch →
    ∃ t ≤ work, LoopRun T (ready false) (startLabel first) .iteration s records t
      ((nativeCall T s).map fun (rep, tail) => ([rep], tail))

private theorem dispatch_eq (T : Template p r k) (s : Snapshot w p r k) (steps : ℕ)
    (hd : SiteTests.iteration.eval s.tests = .dispatch) :
    nativeLoop T steps s = match steps with
    | 0 => none
    | j+1 => collectCall (nativeCall T s) (fun rep tail =>
        runSiteLoop (T.instantiate w s.pub).program s.publicFuel s.publicH s.boundary.val
          s.cap.val j (s.tests.cut.advance [rep]) (s.siteLeft-(1+rep.probes)) tail) := by
  have h := SiteTests.runSiteLoop_at_exit (T.instantiate w s.pub).program s.publicFuel s.publicH steps s.siteLeft s.tests
  rw [hd] at h
  exact h

private theorem dispatch_run {T : Template p r k} {ready : Bool → BoundaryInvariant w p r k}
    {work : ℕ} (call : StartRuns T ready work) (steps : ℕ) (first : Bool) (s : Snapshot w p r k)
    (records : List (WordRecord w)) (hadm : ready first s records) (hleft : s.siteLeft ≤ steps)
    (hd : SiteTests.iteration.eval s.tests = .dispatch)
    (ih : ∀ j < steps, ∀ u ys, ready false u ys → u.siteLeft ≤ j →
      ∃ b ≤ (j+1)*(work+(40*w+30)),
        LoopRun T (ready false) .iteration .finalCheck u ys b (nativeLoop T j u)) :
    ∃ n ≤ work+steps*(work+(40*w+30)),
      LoopRun T (ready false) (startLabel first) .finalCheck s records n (nativeLoop T steps s) := by
  obtain ⟨t, ht, run⟩ := call first s records hadm hd
  rw [dispatch_eq T s steps hd]
  cases hc : nativeCall T s with
  | none =>
    rw [hc] at run
    cases steps <;> exact ⟨t, by omega, run⟩
  | some z =>
    obtain ⟨rep, tail⟩ := z
    rw [hc] at run
    obtain ⟨u, ys, hready, progress, hr⟩ := run
    have hcharge : 1+rep.probes ≤ s.siteLeft := (runChargedCall_iff.mp hc).2.2.2.1
    cases steps with
    | zero => omega
    | succ j =>
      have hl : u.siteLeft ≤ j := by
        have he := progress.siteLeft
        simp [RAMBuckets.cost] at he
        omega
      obtain ⟨b, hb, hrest⟩ := ih j (by omega) u ys hready hl
      have hnext := LoopRun.prependReport hr progress hrest
      rw [nativeLoop_next T progress j] at hnext
      exact ⟨t+b, by omega, hnext⟩

/-- From the iteration test through the entire remaining bucket. The
singleton progress returned by each native call composes into the complete
ordered list of reports and emitted probe records. -/
theorem iteration_loop {T : Template p r k} {ready : Bool → BoundaryInvariant w p r k} {work : ℕ}
    (call : StartRuns T ready work) (steps : ℕ) (s : Snapshot w p r k)
    (records : List (WordRecord w)) (hadm : ready false s records) (hleft : s.siteLeft ≤ steps) :
    ∃ t ≤ (steps+1)*(work+(40*w+30)),
      LoopRun T (ready false) .iteration .finalCheck s records t (nativeLoop T steps s) := by
  induction steps using Nat.strong_induction_on generalizing s records with
  | h n ih =>
    obtain ⟨a, ha, run⟩ := iteration_run T s
    cases hd : SiteTests.iteration.eval s.tests with
    | reject =>
      rw [hd] at run
      have hnone : nativeLoop T n s = none := by
        have h := SiteTests.runSiteLoop_at_exit (T.instantiate w s.pub).program s.publicFuel s.publicH n s.siteLeft s.tests
        rw [hd] at h
        exact h
      rw [hnone]
      exact ⟨a, by rw [Nat.add_mul]; omega, _, _, run, reject_row T⟩
    | finish =>
      rw [hd] at run
      have hdone : nativeLoop T n s = some ([],s.choices) := by
        have h := SiteTests.runSiteLoop_at_exit (T.instantiate w s.pub).program s.publicFuel s.publicH n s.siteLeft s.tests
        rw [hd] at h
        exact h
      rw [hdone]
      exact ⟨a, by rw [Nat.add_mul]; omega, s, records, hadm, Progress.nil s records, run⟩
    | dispatch =>
      rw [hd] at run
      obtain ⟨b, hb, hloop⟩ := dispatch_run call n false s records hadm hleft hd ih
      exact ⟨a+b, by rw [Nat.add_mul]; omega, hloop.prepend run⟩

theorem first_loop {T : Template p r k} {ready : Bool → BoundaryInvariant w p r k} {work : ℕ}
    (call : StartRuns T ready work) (steps : ℕ) (s : Snapshot w p r k)
    (records : List (WordRecord w)) (hadm : ready true s records) (hleft : s.siteLeft ≤ steps)
    (hd : SiteTests.iteration.eval s.tests = .dispatch) :
    ∃ t ≤ work+steps*(work+(40*w+30)),
      LoopRun T (ready false) .first .finalCheck s records t (nativeLoop T steps s) :=
  dispatch_run call steps true s records hadm hleft hd (fun j _ => iteration_loop call j)

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
