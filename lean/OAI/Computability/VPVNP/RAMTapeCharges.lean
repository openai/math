import OAI.Computability.VPVNP.RAMTapeChargesControl
import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-!
# Precharging startup, probes and instruction dispatch

The local verifier pays for a dispatch before reading a program row, and
pays for each call startup or probe before using any read guesses or writing
a probe record. Failed checks enter the rejecting halt. The normal charge
decrements both unary allowances and the binary global allowance and
increments the binary cumulative cost.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Charges

open BurstRAM TapeWord

variable {w : ℕ}

private abbrev marks (n : ℕ) := List.replicate n true

/-- The instruction, call and site caps have one mark per remaining unit.
The global allowance and cumulative cost each occupy exactly one word. -/
def bank (fuel call site : ℕ) (g c : Word w) : Stacks Port :=
  (Data.mk (marks fuel) (marks call) (marks site) (wordBits g) (wordBits c) []).stacks

theorem dispatchRun (fuel call site : ℕ) (g c : Word w) :
    StackRuns code 1 .dispatch (bank (fuel+1) call site g c) .done (bank fuel call site g c) := by
  exact prepend rfl (.nil ..)

theorem dispatchReject (call site : ℕ) (g c : Word w) :
    StackRuns code 1 .dispatch (bank 0 call site g c) .reject (bank 0 call site g c) := by
  exact prepend rfl (.nil ..)

private theorem enterScan (fuel call site : ℕ) (g c : Word w) :
    StackRuns code 2 .charge (bank fuel (call + 1) (site + 1) g c)
      (.scan false true) (bank fuel call site g c) := by
  exact prepend rfl (prepend rfl (.nil ..))

private theorem chargeGlobal (fuel call site : ℕ) (g c : Word w) (hg : 0 < g.val) :
    StackRuns code (4*w+2) (.scan false true) (bank fuel call site g c)
      (.scan true true) (bank fuel call site (prevWord g) c) := by
  have h := adjustRun false true (wordBits g) (marks fuel) (marks call) (marks site) (wordBits c)
  simp only [length_wordBits, adjust_dec_word g hg] at h
  exact h

/-- The successful path takes exactly two unary pops and two linear binary
updates. Startup and probes have the same one-unit effect on these caps. -/
theorem chargeRun (fuel call site : ℕ) (g c : Word w)
    (hg : 0 < g.val) (hc : c.val + 1 < 2 ^ w) :
    StackRuns code (8*w+6) .charge (bank fuel (call+1) (site+1) g c) .done
      (bank fuel call site (prevWord g) ⟨c.val + 1, hc⟩) := by
  have hup := adjustRun true true (wordBits c) (marks fuel) (marks call) (marks site)
    (wordBits (prevWord g))
  simp only [length_wordBits, adjust_inc_word c hc] at hup
  rw [show 8*w+6 = 2 + (4*w+2) + (4*w+2) by omega]
  exact ((enterScan fuel call site g c).trans (chargeGlobal fuel call site g c hg)).trans hup

/-- The first failed allowance determines where execution stops. A final
overflow after both unary pops and the global decrement takes the full cost. -/
def failureTicks (call site : ℕ) (g : Word w) : ℕ :=
  if call = 0 then 1 else if site = 0 then 2 else if g.val = 0 then 4*w+4 else 8*w+6

theorem failureTicks_le (call site : ℕ) (g : Word w) : failureTicks call site g ≤ 8*w+6 := by
  unfold failureTicks
  split <;> (try split) <;> (try split) <;> omega

/-- Every exhausted budget and every cost overflow reaches the actual
rejecting row, with the exact stopping cost of the precharge. -/
theorem chargeReject (fuel call site : ℕ) (g c : Word w)
    (hbad : call = 0 ∨ site = 0 ∨ g.val = 0 ∨ 2 ^ w ≤ c.val + 1) :
    ∃ out, StackRuns code (failureTicks call site g) .charge (bank fuel call site g c) .reject out := by
  cases call with
  | zero => exact ⟨_, prepend rfl (.nil ..)⟩
  | succ a =>
    cases site with
    | zero => exact ⟨_, prepend rfl (prepend rfl (.nil ..))⟩
    | succ s =>
      have h0 := enterScan fuel a s g c
      by_cases hg : g.val = 0
      · have hf := (adjust_borrow_iff (wordBits g)).mpr (by simpa only [value_wordBits] using hg)
        have h := adjustRun false true (wordBits g) (marks fuel) (marks a) (marks s) (wordBits c)
        simp only [hf, length_wordBits] at h
        refine ⟨(scanData false (marks fuel) (marks a) (marks s) (wordBits c)
          (adjust false true (wordBits g)).1 []).stacks, ?_⟩
        simp only [failureTicks, Nat.succ_ne_zero, hg, ↓reduceIte]
        rw [
          show 4*w+4 = 2 + (4*w+2) by omega]
        exact h0.trans h
      · have hc : 2 ^ w ≤ c.val + 1 := by omega
        have hf := (adjust_overflow_iff (wordBits c)).mpr (by simpa only [value_wordBits, length_wordBits] using hc)
        have h := adjustRun true true (wordBits c) (marks fuel) (marks a) (marks s)
          (wordBits (prevWord g))
        simp only [hf, length_wordBits] at h
        refine ⟨(scanData true (marks fuel) (marks a) (marks s) (wordBits (prevWord g))
          (adjust true true (wordBits c)).1 []).stacks, ?_⟩
        simp only [failureTicks, Nat.succ_ne_zero, hg, ↓reduceIte]
        rw [
          show 8*w+6 = 2 + (4*w+2) + (4*w+2) by omega]
        exact (h0.trans (chargeGlobal fuel a s g c (by omega))).trans h

/-- Redirect the successful halt to a normal return while keeping the
rejecting halt and all stack updates on the named ports. -/
def routine {K : Type} (ports : Port → K) (entry : State) : FiniteRoutine K :=
  FiniteRoutine.ofStackCode code ports entry (fun q => decide (q = .done))

/-- Lifting also covers an execution ending at the rejecting control state.
Every port outside the image of `ports` keeps its initial stack. -/
theorem liftRun {K : Type} [DecidableEq K] {ports : Port → K} (hp : Function.Injective ports)
    (base : Stacks K) {n : ℕ} {entry exit : State} (he : entry ≠ .done)
    {s t : Stacks Port} (hr : StackRuns code n entry s exit t) :
    StackRuns (routine ports entry).body.standalone n (some entry) (installStacks ports base s)
      (if exit = .done then none else some exit) (installStacks ports base t) := by
  let labels (q : State) := if q = .done then none else some q
  have hc (q : State) (hn : (code q).returns = false) :
      (routine ports entry).body.standalone (labels q) = (code q).rename ports labels := by
    have hq : q ≠ .done := by rintro rfl; contradiction
    simp [routine, FiniteRoutine.ofStackCode, FiniteRoutine.ofRoutine, Routine.standalone,
      Routine.close, labels, hq]
  have h := hr.lift ports hp labels base hc
  rw [show labels entry = some entry by simp [labels, he]] at h
  exact h

@[simp] theorem routine_rejects {K : Type} (ports : Port → K) (entry : State) :
    (routine ports entry).body.standalone (some .reject) = .halt false := rfl

end RAMTape.Charges

end VPVNP
end Computability
end OAI
