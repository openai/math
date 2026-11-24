import OAI.Computability.VPVNP.RAMLoggedSite
import Mathlib.Tactic.Ring

/-!
# Word work of the finite instruction interpreter

The instruction charges follow the actual local run, including a failed call.
The bound is uniform in the incoming persistent state, probe allowances, and
bits. All arithmetic in the private machine is on words and all operands have
constant arity.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM.PrivateRAM

open VPVNP.BurstRAM

variable {w p r k : ℕ} {C : Type*}

/-- Which invocation follows the current dispatch. A rejected probe, a short
choice stream, or a terminating instruction has no successor invocation. -/
private def continueCall : CallAction w C → ℕ → List Bool → Option (C × ℕ × List Bool)
  | .localStep next, a, bs => some (next, a, bs)
  | .branch _, _, [] => none
  | .branch next, a, b :: bs => some (next b, a, bs)
  | .read _ _, 0, _ => none
  | .read _ next, a + 1, bs => (takeWord w bs).map fun (v, rest) => (next v, a, rest)
  | .write .., 0, _ => none
  | .write _ _ next, a + 1, bs => some (next, a, bs)
  | .finish _, _, _ | .reject, _, _ => none

private theorem instructionCount_succ (P : Program w C) (fuel : ℕ) (c : C)
    (a : ℕ) (bits : List Bool) :
    (runLocalCall P (fuel + 1) c a bits).instructions =
      1 + match continueCall (P.step c) a bits with
        | none => 0
        | some (c', a', bs) => (runLocalCall P fuel c' a' bs).instructions := by
  cases hs : P.step c with
  | finish result | reject | localStep next =>
    simp [hs, continueCall, runLocalCall, LocalCallRun.prepend, LocalCallRun.stop]
  | branch next =>
    cases bits <;> simp [hs, continueCall, runLocalCall, LocalCallRun.prepend, LocalCallRun.stop]
  | read addr next =>
    cases a with
    | zero => simp [hs, continueCall, runLocalCall, LocalCallRun.stop]
    | succ a =>
      cases h : takeWord w bits with
      | none => simp [hs, h, continueCall, runLocalCall, LocalCallRun.stop]
      | some pair =>
        obtain ⟨v, rest⟩ := pair
        simp [hs, h, continueCall, runLocalCall, LocalCallRun.prepend]
  | write addr v next =>
    cases a <;> simp [hs, continueCall, runLocalCall, LocalCallRun.stop, LocalCallRun.prepend]

/-- A private load scans at most the number of write-log slots reserved
for this call. A store prepends its address and value. -/
def Instr.logCharge (i : Instr w p r k) (capacity : ℕ) : ℕ :=
  match i with
  | .loadPrivate .. => 4 * (capacity + 1)
  | .storePrivate .. => 3
  | _ => 0

theorem Instr.logCharge_le (i : Instr w p r k) (capacity : ℕ) :
    i.logCharge capacity ≤ 4 * (capacity + 1) := by
  cases i <;> simp [Instr.logCharge]
  omega

/-- Sum the elementary opcode charges actually incurred by the local call.
The final dispatched instruction counts even when it causes rejection. -/
def Machine.dispatchWork (M : Machine w p r k) (capacity : ℕ) : ℕ → Config w p r → ℕ → List Bool → ℕ
  | 0, _, _, _ => 0
  | f + 1, c, a, bs =>
    ((M.code c.pc).wordWork + (M.code c.pc).logCharge capacity) + match continueCall (M.program.step c) a bs with
      | none => 0
      | some (c', a', tail) => M.dispatchWork capacity f c' a' tail

theorem Machine.dispatchWork_le (M : Machine w p r k) (capacity fuel : ℕ) (c : Config w p r)
    (a : ℕ) (bits : List Bool) :
    M.dispatchWork capacity fuel c a bits ≤ (6 + 4 * (capacity + 1)) * (runLocalCall M.program fuel c a bits).instructions := by
  induction fuel generalizing c a bits with
  | zero => simp [Machine.dispatchWork, runLocalCall]
  | succ f ih =>
    rw [Machine.dispatchWork, instructionCount_succ, Nat.mul_add, Nat.mul_one]
    have hi := Nat.add_le_add (M.code c.pc).wordWork_le ((M.code c.pc).logCharge_le capacity)
    cases h : continueCall (M.program.step c) a bits with
    | none => simpa using hi
    | some t =>
      obtain ⟨c', a', tail⟩ := t
      exact Nat.add_le_add hi (ih c' a' tail)

private theorem continueCall_mapState {D : Type*} (f : C → D) (action : CallAction w C)
    (allowance : ℕ) (bits : List Bool) :
    continueCall (action.mapState f) allowance bits =
      (continueCall action allowance bits).map (fun (c, a, bs) => (f c, a, bs)) := by
  cases action with
  | finish | reject | localStep => rfl
  | branch => cases bits <;> rfl
  | write => cases allowance <;> rfl
  | read =>
    cases allowance with
    | zero => rfl
    | succ a =>
      simp only [continueCall, CallAction.mapState, Option.map_map]
      rfl

theorem Instr.actualLogWork_le (i : Instr w p r k) (l : LogConfig w p r) {capacity : ℕ}
    (h : l.writes.length ≤ capacity) : i.actualLogWork l ≤ i.logCharge capacity := by
  cases i <;> simp only [Instr.actualLogWork, Instr.logCharge, le_refl]
  exact (WriteLog.scan_work_le ..).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right h 1))

/-- Opcode work in the implementation with a concrete write log. -/
def Machine.loggedDispatchWork (M : Machine w p r k) : ℕ → LogConfig w p r → ℕ → List Bool → ℕ
  | 0, _, _, _ => 0
  | f + 1, l, a, bs =>
    ((M.code l.pc).wordWork + (M.code l.pc).actualLogWork l) +
      match continueCall (M.logProgram.step l) a bs with
      | none => 0
      | some (l', a', tail) => M.loggedDispatchWork f l' a' tail

private theorem Machine.continue_writes (M : Machine w p r k) (l : LogConfig w p r) {a bits l' a' tail}
    (h : continueCall (M.logProgram.step l) a bits = some (l', a', tail)) :
    l'.writes = (M.code l.pc).nextLog l := by
  simp only [Machine.logProgram, Instr.runLogged, continueCall_mapState, Option.map_eq_some_iff] at h
  obtain ⟨⟨_, _, _⟩, _, he⟩ := h
  cases he
  rfl

/-- The reserved linear scans bound the actual linear scans on *every* choice
stream. The invariant pays for at most one new private write per dispatch. -/
theorem Machine.loggedDispatchWork_le (M : Machine w p r k) (fuel : ℕ) (l : LogConfig w p r)
    (a : ℕ) (bits : List Bool) {capacity : ℕ} (hcap : l.writes.length + fuel ≤ capacity) :
    M.loggedDispatchWork fuel l a bits ≤ M.dispatchWork capacity fuel l.denote a bits := by
  induction fuel generalizing l a bits with
  | zero => simp [Machine.loggedDispatchWork, Machine.dispatchWork]
  | succ f ih =>
    rw [Machine.loggedDispatchWork, Machine.dispatchWork, ← M.logProgram_step,
      continueCall_mapState]
    apply Nat.add_le_add
    · exact Nat.add_le_add_left ((M.code l.pc).actualLogWork_le l (by omega)) _
    · cases h : continueCall (M.logProgram.step l) a bits with
      | none => rfl
      | some t =>
        obtain ⟨l', a', tail⟩ := t
        apply ih
        rw [M.continue_writes l h]
        have := (M.code l.pc).nextLog_length_le l
        omega

/-- Each call starts with an empty log; its instruction fuel is enough log
capacity even on rejecting paths. -/
theorem Machine.loggedDispatchWork_start (M : Machine w p r k) (fuel a : ℕ) (s : Word w) (bs : List Bool) :
    M.loggedDispatchWork fuel (M.logProgram.start s) a bs ≤
      M.dispatchWork fuel fuel (M.program.start s) a bs :=
  M.loggedDispatchWork_le fuel (M.logProgram.start s) a bs (by simp [Machine.logProgram])

private def CallFrame.continuation : CallFrame w C → Option (C × ℕ × List Bool)
  | .stop _ => none
  | .next _ c a bs => some (c, a, bs)

private theorem CallFrame.continuation_eq (action : CallAction w C) (a : ℕ) (bs : List Bool) :
    (CallFrame.ofAction action a bs).continuation = continueCall action a bs := by
  cases action with
  | finish | reject | localStep => rfl
  | branch => cases bs <;> rfl
  | write => cases a <;> rfl
  | read =>
    cases a with
    | zero => rfl
    | succ a =>
      cases h : takeWord w bs with
      | none => simp [CallFrame.ofAction, CallFrame.continuation, continueCall, h]
      | some pair =>
        obtain ⟨v, tail⟩ := pair
        simp [CallFrame.ofAction, CallFrame.continuation, continueCall, h]

theorem Machine.meteredLoggedCall_work_eq (M : Machine w p r k) (f : ℕ) (l : LogConfig w p r)
    (a : ℕ) (bs : List Bool) :
    (M.meteredLoggedCall f l a bs).2 = M.loggedDispatchWork f l a bs +
      LocalCharge (M.meteredLoggedCall f l a bs).1 := by
  induction f generalizing l a bs with
  | zero => rfl
  | succ f ih =>
    rw [Machine.meteredLoggedCall, Instr.meteredAction_spec, Machine.loggedDispatchWork,
      ← CallFrame.continuation_eq]
    dsimp only
    change ((match CallFrame.ofAction (M.logProgram.step l) a bs with
      | .stop t => (t, _)
      | .next e c a' tail => ((M.meteredLoggedCall f c a' tail).1.prepend e, _))
        : LocalCallRun w × ℕ).2 = _
    cases h : CallFrame.ofAction (M.logProgram.step l) a bs with
    | stop t =>
      change _ = _ + LocalCharge ((match CallFrame.ofAction (M.logProgram.step l) a bs with
        | .stop out => (out, _)
        | .next e c a' tail => ((M.meteredLoggedCall f c a' tail).1.prepend e, _))
          : LocalCallRun w × ℕ).1
      rw [h]
      rfl
    | next e c a' tail =>
      change _ = _ + LocalCharge ((match CallFrame.ofAction (M.logProgram.step l) a bs with
        | .stop out => (out, _)
        | .next e c a'' tail' => ((M.meteredLoggedCall f c a'' tail').1.prepend e, _))
          : LocalCallRun w × ℕ).1
      rw [h]
      dsimp only [CallFrame.continuation]
      rw [ih c a' tail, localCharge_prepend]
      omega

/-- Besides opcode work, reserve eight control operations per dispatch,
five word stores per occupied probe record, and four operations per bit
guessed, fetched and packed into a word. -/
def Machine.callWordWork (M : Machine w p r k) (fuel : ℕ) (c : Config w p r)
    (allowance : ℕ) (bits : List Bool) : ℕ :=
  let t := runLocalCall M.program fuel c allowance bits
  M.dispatchWork fuel fuel c allowance bits + 8 * t.instructions + 5 * t.probes + 4 * t.guessWork

/-- On a fresh call the actual one-pass work is bounded by the reserved
work, including truncated streams and attempted over-cap probes. -/
theorem Machine.meteredLoggedCall_work_le (M : Machine w p r k) (fuel : ℕ) (s : Word w)
    (allowance : ℕ) (bits : List Bool) :
    (M.meteredLoggedCall fuel (M.logProgram.start s) allowance bits).2 ≤
      M.callWordWork fuel (M.program.start s) allowance bits := by
  rw [M.meteredLoggedCall_work_eq, M.meteredLoggedCall_result, M.logProgram_start]
  have h := M.loggedDispatchWork_start fuel allowance s bits
  dsimp only [Machine.callWordWork, LocalCharge]
  omega

theorem Machine.callWordWork_le_units (M : Machine w p r k) (fuel : ℕ) (c : Config w p r)
    (allowance : ℕ) (bits : List Bool) :
    let t := runLocalCall M.program fuel c allowance bits
    M.callWordWork fuel c allowance bits ≤ (16 * (fuel + 2)) * (t.instructions + t.probes + t.guessWork) := by
  let t := runLocalCall M.program fuel c allowance bits
  have h := M.dispatchWork_le fuel fuel c allowance bits
  change M.dispatchWork fuel fuel c allowance bits ≤ (6 + 4 * (fuel + 1)) * t.instructions at h
  change M.dispatchWork fuel fuel c allowance bits + 8*t.instructions + 5*t.probes + 4*t.guessWork ≤ _
  calc
    _ ≤ (6 + 4 * (fuel + 1) + 8) * t.instructions + 5*t.probes + 4*t.guessWork := by
      rw [Nat.add_mul]; omega
    _ ≤ (16*(fuel+2))*t.instructions + (16*(fuel+2))*t.probes + (16*(fuel+2))*t.guessWork :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
        (Nat.mul_le_mul_right _ (by omega))) (Nat.mul_le_mul_right _ (by omega))
    _ = _ := by simp only [Nat.mul_add, t]

theorem Machine.callWordWork_le (M : Machine w p r k) (fuel : ℕ) (c : Config w p r)
    (allowance : ℕ) (bits : List Bool) :
    M.callWordWork fuel c allowance bits ≤ (16 * (fuel + 2)) * (3 * fuel + w * allowance) :=
  (M.callWordWork_le_units ..).trans
    (Nat.mul_le_mul_left _ (runLocalCall_totalWork_le M.program fuel c allowance bits))

private theorem Machine.loggedChargedCall_work_le_units (M : Machine w p r k) (fuel : ℕ) (s : Word w)
    (callLeft globalLeft siteLeft : ℕ) (bits : List Bool) :
    let t := runChargedCall M.program fuel (M.program.start s) callLeft globalLeft siteLeft bits
    (M.loggedChargedCall fuel s callLeft globalLeft siteLeft bits).2 ≤
      (16 * (fuel + 2)) * (t.instructions + t.probes + t.guessWork) := by
  cases h : min callLeft (min globalLeft siteLeft) with
  | zero => simp [Machine.loggedChargedCall, runChargedCall, h]
  | succ a =>
    simpa [Machine.loggedChargedCall, runChargedCall, h] using
      (M.meteredLoggedCall_work_le fuel s a bits).trans (M.callWordWork_le_units fuel (M.program.start s) a bits)

/-- Count the elementary work of the same invocation that returns the site's
reports and unused bits. -/
def Machine.siteWordWork (M : Machine w p r k) (fuel H boundary globalCap steps : ℕ)
    (c : Cut w) (siteLeft : ℕ) (bits : List Bool) : ℕ :=
  (M.runLoggedSite fuel H boundary globalCap steps c siteLeft bits).work

theorem Machine.siteWordWork_le_units (M : Machine w p r k) (fuel H boundary globalCap steps : ℕ)
    (c : Cut w) (siteLeft : ℕ) (bits : List Bool) :
    M.siteWordWork fuel H boundary globalCap steps c siteLeft bits ≤
      (16 * (fuel + 2)) * (meteredSiteLoop M.program 1 fuel H boundary globalCap steps c siteLeft bits).work := by
  unfold Machine.siteWordWork
  induction steps generalizing c siteLeft bits with
  | zero =>
    rw [Machine.runLoggedSite, meteredSiteLoop]
    by_cases hc : c.cost ≤ globalCap
    · cases c.state <;> simp only [hc, ↓reduceIte]
      · simp
      · split <;> simp
    · simp [hc]
  | succ n ih =>
    rw [Machine.runLoggedSite, meteredSiteLoop]
    by_cases hc : c.cost ≤ globalCap
    · cases hs : c.state with
      | none => simp [hc]
      | some s =>
        by_cases hb : c.cost < boundary
        · simp only [hc, hb, ↓reduceIte, Machine.loggedChargedCall_result]
          have hw := M.loggedChargedCall_work_le_units fuel s H (globalCap - c.cost) siteLeft bits
          dsimp only at hw
          cases ht : (runChargedCall M.program fuel (M.program.start s) H
              (globalCap - c.cost) siteLeft bits).output with
          | none =>
            change 16 + _ ≤ (16 * (fuel+2)) * (1 + _)
            rw [Nat.mul_add, Nat.mul_one]
            exact Nat.add_le_add (by omega) hw
          | some z =>
            obtain ⟨report, tail⟩ := z
            let t := runChargedCall M.program fuel (M.program.start s) H (globalCap-c.cost) siteLeft bits
            let charge := 1 + t.probes
            have htail := ih ⟨c.cost+charge, report.result⟩ (siteLeft-charge) tail
            change 16 + _ + _ ≤ (16 * (fuel+2)) * ((1 + _) + _)
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
            exact Nat.add_le_add (Nat.add_le_add (by omega) hw) htail
        · simp [hc, hb]
    · simp [hc]

theorem Machine.siteWordWork_le (M : Machine w p r k) (fuel H boundary globalCap steps : ℕ)
    (c : Cut w) (siteLeft : ℕ) (bits : List Bool) :
    M.siteWordWork fuel H boundary globalCap steps c siteLeft bits ≤
      (16 * (fuel + 2)) * ((steps + 1) * (1 + 3 * fuel + w * H)) :=
  (M.siteWordWork_le_units ..).trans (Nat.mul_le_mul_left _ (siteWork_le ..))

/-- The metered result of the concrete word interpreter and its private
memory log. The successful reports and unused bits are the ordinary site's
output, including on malformed incoming data. -/
def Machine.privateSite (M : Machine w p r k) (fuel H boundary globalCap steps : ℕ)
    (c : Cut w) (siteLeft : ℕ) (bits : List Bool) : MeteredSiteRun w :=
  M.runLoggedSite fuel H boundary globalCap steps c siteLeft bits

theorem Machine.privateSite_output (M : Machine w p r k) (fuel H boundary globalCap steps : ℕ)
    (c : Cut w) (siteLeft : ℕ) (bits : List Bool) :
    (M.privateSite fuel H boundary globalCap steps c siteLeft bits).output =
      runSiteLoop M.program fuel H boundary globalCap steps c siteLeft bits :=
  M.runLoggedSite_output ..

/-- The site portion of the paper's clock bound when the bucket size is at
most twice the instruction fuel. For fuel `n^u`, `u ≥ 1`, this follows from
`H ≤ 2n`. The constant leaves room for the remaining validation checks. -/
theorem Machine.privateSite_work_le (M : Machine w p r k) {fuel H : ℕ} (hH : H ≤ 2 * fuel)
    (boundary globalCap : ℕ) (c : Cut w) (siteLeft : ℕ) (bits : List Bool) :
    (M.privateSite fuel H boundary globalCap (2*H-1) c siteLeft bits).work ≤
      256 * (H+1) * (fuel+1) * (fuel+1) * (w+2) := by
  have hinner : 1 + 3*fuel + w*H ≤ 4*(fuel+1)*(w+2) := by
    have := Nat.mul_le_mul_left w hH
    ring_nf at *
    omega
  calc
    _ ≤ (16*(fuel+2))*((2*H-1+1)*(1+3*fuel+w*H)) := M.siteWordWork_le ..
    _ ≤ (16*(2*(fuel+1)))*((2*(H+1))*(4*(fuel+1)*(w+2))) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul (by omega) hinner)
    _ = _ := by ring

end BurstRAM.PrivateRAM

end VPVNP
end Computability
end OAI
