import OAI.Computability.BorderVNP.TeamLocalClockStartup
import OAI.Computability.BorderVNP.TeamLocalClockFinish

/-!
# Exact physical startup on a verified shared message

The accepting sender fixes the raw bits even if an arbitrary witness supplies
its execution time and final bank. The receiving program then has a unique
terminal outcome, bank and instruction count. This covers bad PC values, clock
overruns, accepting halts and live continuations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamLocalClock.Startup

open VPVNP RAMTape BurstRAM TeamTapeHandoff RAMTape.PublicExprMachine
open TeamLocalClockPC (Outcome)

variable {p r k w : ℕ}

/-- Terminal dispatch outcome for the local predecessor's actual frame. -/
def result (p : ℕ) (f : Frame w r) (limit : Word w) : Outcome p :=
  if f.elapsed ≤ limit then
    match f with
    | .live pc _ _ => TeamLocalClockPC.lookup p pc.val
    | .accepted _ => .accepted
  else .reject

/-- Only a valid, continuing instruction table entry consumes the startup subtraction. -/
def remaining (p : ℕ) (f : Frame w r) (limit : Word w) : Word w :=
  match f with
  | .live pc _ t => if pc.val < p ∧ t ≤ limit then packed w (limit.val - t.val) else limit
  | .accepted _ => limit

/-- One width-quadratic clock for all startup branches of a fixed register count. -/
def budget (r w : ℕ) : ℕ := (8 * r + 200) * (w + 1) ^ 2

private theorem budget_bound (r w : ℕ) :
    (r + 2) * (6 * w + 2) + 3 + (4 * w + 4) + (8 * w + 2 + 150 * (w + 1) ^ 2) ≤
      budget r w := by
  unfold budget
  nlinarith [Nat.zero_le (r * w), Nat.zero_le (r * w ^ 2), Nat.zero_le (w ^ 2)]

/-- Every canonical candidate has a concrete terminal run at the asserted bank.
The shared bound covers all live and propagated-halt cases. -/
theorem run (p : ℕ) (fits : p ≤ 2 ^ w) (pub : Fin k → Word w) (f : Frame w r)
    (H limit max : Word w) (suffix : List Bool) :
    ∃ t ≤ budget r w, StackRuns (code p r k) t (entry p r)
      (input pub H limit max (f.bits ++ suffix))
      (.done (result p f limit)) (decoded pub f H (remaining p f limit) max suffix) := by
  have cap := budget_bound r w
  cases f with
  | accepted t =>
    exact ⟨_, by omega, halted_run p pub H limit t max suffix⟩
  | live z regs t =>
    by_cases valid : z.val < p
    · let pc : Fin p := ⟨z.val, valid⟩
      have hz : packed w pc.val = z := Fin.ext (packed_val z.isLt)
      have lookup := TeamLocalClockPC.lookup_packed pc fits
      rw [hz] at lookup
      obtain ⟨time, htime, hr⟩ := live_run pub pc fits regs H limit t max suffix
      rw [hz] at hr
      refine ⟨time, htime.trans cap, ?_⟩
      simpa only [result, remaining, Frame.elapsed, valid, true_and, lookup] using hr
    · have bad := Nat.not_lt.mp valid
      have hr := invalidPC_run pub z t regs H limit max suffix bad
      refine ⟨(r + 2) * (6 * w + 2) + 3 + (4 * w + 4), by omega, ?_⟩
      simpa only [result, remaining, valid, false_and, ite_false, Frame.elapsed,
        (TeamLocalClockPC.lookup_reject_iff ..).mpr bad, ite_self] using hr

private theorem step_continues {K Q : Type*} [DecidableEq K] {c : StackCode K Q}
    {q q' : Q} {s s' : Stacks K} (h : StackStep c q s q' s') : (c q).returns = false := by
  cases h <;> simp_all

private theorem step_unique {K Q : Type*} [DecidableEq K] {c : StackCode K Q}
    {q a b : Q} {s x y : Stacks K} (left : StackStep c q s a x) (right : StackStep c q s b y) :
    a = b ∧ x = y := by
  cases left <;> cases right <;> simp_all

private theorem terminal_unique {K Q : Type*} [DecidableEq K] {c : StackCode K Q}
    {q a b : Q} {s x y : Stacks K} {m n : ℕ}
    (first : StackRuns c m q s a x) (hf : (c a).returns = true)
    (second : StackRuns c n q s b y) (hs : (c b).returns = true) : m = n ∧ a = b ∧ x = y := by
  induction first generalizing n b y with
  | nil =>
    cases second with
    | nil => exact ⟨rfl, rfl, rfl⟩
    | cons h _ => exact Bool.noConfusion (hf.symm.trans (step_continues h))
  | cons l _ ih =>
    cases second with
    | nil => exact Bool.noConfusion (hs.symm.trans (step_continues l))
    | cons r rest =>
      obtain ⟨rfl, rfl⟩ := step_unique l r
      obtain ⟨rfl, rfl, rfl⟩ := ih hf rest hs
      exact ⟨rfl, rfl, rfl⟩

/-- The physical candidate admits one typed interpretation and one timed startup result.
The full output bank includes all word fields and the untouched incident suffix. -/
def ExactReception (p : ℕ) (pub : Fin k → Word w) (f : Frame w r)
    (H limit max : Word w) (raw suffix : List Bool) : Prop :=
    (∀ g : Frame w r, g.bits = raw ↔ g = f) ∧
      ∃ t ≤ budget r w, StackRuns (code p r k) t (entry p r) (input pub H limit max (raw ++ suffix))
          (.done (result p f limit)) (decoded pub f H (remaining p f limit) max suffix) ∧
        ∀ (t' : ℕ) (o : Outcome p) (s' : Stacks (Port r k)),
          StackRuns (code p r k) t' (entry p r) (input pub H limit max (raw ++ suffix))
            (.done o) s' →
          t' = t ∧ o = result p f limit ∧
            s' = decoded pub f H (remaining p f limit) max suffix

private theorem exact_of_bits (p : ℕ) (fits : p ≤ 2 ^ w) (pub : Fin k → Word w)
    (f : Frame w r) (H limit max : Word w) (raw suffix : List Bool) (bits : f.bits = raw) :
    ExactReception p pub f H limit max raw suffix := by
  subst raw
  refine ⟨fun g => Frame.bits_injective.eq_iff, ?_⟩
  obtain ⟨t, ht, hr⟩ := run p fits pub f H limit max suffix
  refine ⟨t, ht, hr, ?_⟩
  intro t' o s' other
  have done (v : Outcome p) : (code p r k (.done v)).returns = true := by cases v <;> rfl
  obtain ⟨ht', hv, hs⟩ := terminal_unique other (done _) hr (done _)
  exact ⟨ht', State.done.inj hv, hs⟩

/-- For any accepting sender witness and any receiver witness starting on the same raw
link, all terminal fields, dispatch outcome and elapsed physical runtime agree. -/
theorem verified_receiver_exact (p : ℕ) (fits : p ≤ 2 ^ w) (pub : Fin k → Word w)
    (f : Frame w r) (H limit max : Word w) (raw suffix : List Bool) {tSend : ℕ}
    {sSend : Stacks (Link.Port r)} (sender : StackRuns (Link.sender r) tSend (Link.entry r)
      (Link.senderBank f raw) (.inr (.done true)) sSend) :
    ExactReception p pub f H limit max raw suffix :=
  exact_of_bits p fits pub f H limit max raw suffix
    ((Link.sender_accept_iff f raw).mp ⟨tSend, sSend, sender⟩)

/-- An accepting execution of the actual clocked finisher fixes the next processor's startup.
The outgoing register bank supplies its PC and elapsed tick. An over-limit halt consequently
has the unique rejecting receiver result even when its outgoing bits are canonical. -/
theorem verified_finish_receiver_exact (mode : Finish.Mode p) (fits : p ≤ 2 ^ w)
    (senderPub pub : Fin k → Word w) (s : PrivateRAM.LogConfig w p r)
    (left global elapsed max H limit : Word w) (stamp raw suffix : List Bool) {tSend : ℕ}
    {sSend : Stacks (Finish.Port r k)}
    (sender : StackRuns Finish.rows tSend (.enter mode false)
      (Finish.bank (banks senderPub s (chargeRegisters left global elapsed 0) max stamp) [] raw)
      (.done true) sSend) :
    ExactReception p pub (Finish.frame mode s.reg elapsed) H limit max raw suffix :=
  exact_of_bits p fits pub _ H limit max raw suffix
    ((Finish.successor_accept_iff mode senderPub s left global elapsed max stamp raw).mp
      ⟨tSend, sSend, sender⟩)

/-- Processor zero has the same uniform clock bound and only its canonical time-zero exit. -/
theorem first_exact (pub : Fin k → Word w) (pc : Fin p) (regs : Fin r → Word w)
    (H limit max : Word w) (suffix : List Bool) :
    let f := initial (packed w pc.val) regs
    let s := decoded pub f H limit max suffix
    1 ≤ budget r w ∧ StackRuns (code p r k) 1 (.first pc) s (.done (.live pc)) s ∧
      ∀ t o s', StackRuns (code p r k) t (.first pc) s (.done o) s' →
        t = 1 ∧ o = .live pc ∧ s' = s := by
  intro f s
  have h := first_run pub pc regs H limit max suffix
  refine ⟨by have := budget_bound r w; omega, h, ?_⟩
  intro t o s' other
  have hd : (code p r k (.done o)).returns = true := by cases o <;> rfl
  obtain ⟨ht, ho, hs⟩ := terminal_unique other hd h rfl
  exact ⟨ht, State.done.inj ho, hs⟩

end TeamLocalClock.Startup

end BorderVNP
end Computability
end OAI
