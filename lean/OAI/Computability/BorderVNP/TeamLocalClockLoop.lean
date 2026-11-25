import OAI.Computability.BorderVNP.TeamLocalClock

/-! # Clocked physical opcode dispatch at a processor boundary

The opcode and its source registers determine the burst length before any
arithmetic updates, probes, private calls or path choices. The live PC label
is retained on a refusal. A successful charge stores the first probe time and
then enters the project's physical opcode implementation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamLocalClock.Loop

open VPVNP RAMTape BurstRAM RAMTape.PublicExprMachine TeamTapeHandoff

variable {w p r k m : ℕ}

/-- Static kind of an instruction at the point where its tick guard runs. -/
inductive Kind (r : ℕ) where
  | accept | reject | ordinary | burst (length : Fin r)
  deriving Fintype

/-- Native halts and forbidden opcodes are terminal; private macros take their burst
length from the named live register. -/
def kind (P : TeamOpcode.Program p r k m) (pc : Fin p) : Kind r :=
  match P.tag pc with
  | .call _ _ len _ | .callReg _ _ len _ => .burst len
  | .sign .. => .ordinary
  | .native => match P.base.code pc with
    | .accept => .accept
    | .reject | .loadPrivate .. | .storePrivate .. | .returnState .. => .reject
    | _ => .ordinary

/-- A refusal retains the fetched PC for the successor; a checked opcode exit requests
the actual callback with its freshly prepared architectural state. -/
inductive Exit (p r m : ℕ) where
  | accepted | reject | handoff (pc : Fin p) | callback (out : TeamOpcode.Exit p r m)
  deriving Fintype

/-- All labels of the fixed pre-callback code. -/
inductive Label (P : TeamOpcode.Program p r k m) where
  | enter (pc : Fin p)
  | size (pc : Fin p) (len : Fin r) (q : SuccessorCap.State)
  | stage (pc : Fin p) (len : Fin r) (q : (stageLength (k := k) len).State)
  | check (pc : Fin p) (q : StepState)
  | clear (out : Exit p r m) (q : (clearMeter (r := r) (k := k)).State)
  | finish (pc : Fin p) (q : (finishCharge (r := r) (k := k)).State)
  | opcode (q : TeamOpcode.Dispatch.Label P)
  | exit (out : Exit p r m)
  deriving Fintype

private def sizePorts (len : Fin r) : TapeWord.ScanPort → Port r k
  | .left => .isa (.reg len)
  | .right => .maxBurst
  | .tmp => .meter (.work 0)
  | .out => .meter (.work 1)

private theorem sizePorts_inj (len : Fin r) : Function.Injective (sizePorts (k := k) len) := by
  intro u v he
  cases u <;> cases v <;> simp_all [sizePorts]

private def sizeLabel {P : TeamOpcode.Program p r k m} (pc : Fin p) (len : Fin r) :
    SuccessorCap.State → Label P
  | .done ok => if ok then .stage pc len (stageLength len).body.entry else .exit .reject
  | q => .size pc len q

private def checkLabel {P : TeamOpcode.Program p r k m} (pc : Fin p) : StepState → Label P
  | .done .handoff => .clear (.handoff pc) clearMeter.body.entry
  | .done .reject => .clear .reject clearMeter.body.entry
  | .done .execute => .finish pc finishCharge.body.entry
  | q => .check pc q

private def opcodeLabel {P : TeamOpcode.Program p r k m} : TeamOpcode.Dispatch.Label P → Label P
  | .exit out => .exit (.callback out)
  | q => .opcode q

/-- The physical guard, charge, timestamp preparation and opcode dispatch share one table.
Its labels depend on the fixed program, not on the word width or processor length. -/
def rows (P : TeamOpcode.Program p r k m) : StackCode (Port r k) (Label P)
  | .enter pc => .goto (match kind P pc with
    | .accept => .exit .accepted
    | .reject => .exit .reject
    | .ordinary => .check pc (.guard (.scan false (.left true)))
    | .burst len => .size pc len (.left true))
  | .size pc len q => (SuccessorCap.code q).rename (sizePorts len) (sizeLabel pc len)
  | .stage pc len q => ((stageLength len).body.code q).rename id
      (fun u => u.elim (.check pc (.guard (.scan false (.left true)))) (.stage pc len))
  | .check pc q => (stepCode q).rename Port.meter (checkLabel pc)
  | .clear out q => (clearMeter.body.code q).rename id (fun u => u.elim (.exit out) (.clear out))
  | .finish pc q => (finishCharge.body.code q).rename id
      (fun u => u.elim (.opcode (.enter pc)) (.finish pc))
  | .opcode q => (TeamOpcode.Dispatch.rows P q).rename Port.isa opcodeLabel
  | .exit _ => .halt false

private theorem installRoutine {K Z : Type} [DecidableEq K] (routine : FiniteRoutine K) (C : StackCode K Z)
    (label : routine.State → Z) (exit : Z) (hc : ∀ q, C (label q) = (routine.body.code q).rename id
      (fun u => u.elim exit label)) {t : ℕ} {s b : Stacks K} (run : routine.Runs t s b) :
    StackRuns C t (label routine.body.entry) s exit b := by
  have h := run.lift id Function.injective_id (fun u => u.elim exit label) s (target := C) (by
    rintro (_ | q) hr
    · contradiction
    · exact hc q)
  have hi (v : Stacks K) : installStacks id s v = v := funext fun j => installStacks_at Function.injective_id s v j
  simpa only [hi, Option.elim_some, Option.elim_none] using h

/-- The literal word limit on a private read is checked against the actual live register
before entering the staging or metering code. -/
theorem size_run (P : TeamOpcode.Program p r k m) (pub : Fin k → Word w) (s : TeamOpcode.State w p r)
    (H left elapsed max : Word w) (len : Fin r) :
    StackRuns (rows P) (8*w+2) (.size s.pc len (.left true)) (bank pub s H left elapsed max)
      (if s.reg len ≤ max then .stage s.pc len (stageLength len).body.entry else .exit .reject)
      (bank pub s H left elapsed max) := by
  have h := SuccessorCap.run_lift (sizePorts len) (sizePorts_inj len) (sizeLabel s.pc len)
    (target := rows P) (by intro u hu; cases u <;> first | rfl | simp [SuccessorCap.code] at hu)
    (bank pub s H left elapsed max)
    (show (wordBits (s.reg len)).length = (wordBits max).length by simp) rfl rfl
  change StackRuns (rows P) (8*(wordBits (s.reg len)).length+2) _ _
    (sizeLabel s.pc len (.done (decide (TapeWord.value (wordBits (s.reg len)) ≤ TapeWord.value (wordBits max))))) _ at h
  simpa only [length_wordBits, TapeWord.value_wordBits, sizeLabel, decide_eq_true_eq, Fin.le_def] using h

private theorem stage_run (P : TeamOpcode.Program p r k m) (pub : Fin k → Word w) (s : TeamOpcode.State w p r)
    (H left elapsed max : Word w) (len : Fin r) :
    StackRuns (rows P) (6*w+3) (.stage s.pc len (stageLength len).body.entry) (bank pub s H left elapsed max)
      (.check s.pc (.guard (.scan false (.left true))))
      (banks pub s.logged (chargeRegisters H left elapsed (s.reg len)) max []) :=
  installRoutine (stageLength (k := k) len) (rows P) (Label.stage s.pc len) _ (fun _ => rfl) (stageLength_runs ..)

private theorem check_run (P : TeamOpcode.Program p r k m) (pub : Fin k → Word w) (s : TeamOpcode.State w p r)
    (H left elapsed q max : Word w) :
    ∃ t ≤ 2*(8*w+2)+600*(w+1)^2, StackRuns (rows P) t (.check s.pc (.guard (.scan false (.left true))))
      (banks pub s.logged (chargeRegisters H left elapsed q) max [])
      (checkLabel s.pc (.done (decision H.val left.val q.val)))
      (banks pub s.logged (if decision H.val left.val q.val = .execute then chargedRegisters H left elapsed q
        else chargeRegisters H left elapsed q) max []) := by
  obtain ⟨t, ht, hr⟩ := step_run H left elapsed q 0 []
  have h := hr.lift Port.meter (fun _ _ he => Port.meter.inj he) (checkLabel s.pc)
    (banks pub s.logged (chargeRegisters H left elapsed q) max []) (target := rows P) (by
      intro z hz; cases z with
      | guard | charge => rfl
      | done d => simp [stepCode] at hz)
  exact ⟨t, ht, by simpa only [install_meter, checkLabel] using h⟩

private theorem opcode_run (P : TeamOpcode.Program p r k m) (pub : Fin k → Word w) (s : TeamOpcode.State w p r)
    (reg : Fin 6 → Word w) (max : Word w) (stamp : List Bool) :
    ∃ t ≤ 110*(w+1)^2, StackRuns (rows P) t (.opcode (.enter s.pc)) (banks pub s.logged reg max stamp)
      (.exit (.callback (TeamOpcode.prepare P pub s).1)) (banks pub (TeamOpcode.prepare P pub s).2 reg max stamp) := by
  obtain ⟨t, ht, run⟩ := TeamOpcode.Dispatch.step P pub s
  have h := run.lift Port.isa (fun _ _ he => Port.isa.inj he) opcodeLabel (banks pub s.logged reg max stamp)
    (target := rows P) (by intro q hq; cases q <;> first | rfl | simp [TeamOpcode.Dispatch.rows] at hq)
  exact ⟨t, ht, by simpa only [install_isa, opcodeLabel] using h⟩

/-- Exact callback and physical bank produced after guard/charge for one staged opcode.
A refused handoff restores the entire entry bank. -/
def afterGuard (P : TeamOpcode.Program p r k m) (pub : Fin k → Word w) (s : TeamOpcode.State w p r)
    (H left elapsed q max : Word w) : Exit p r m × Stacks (Port r k) :=
  match decision H.val left.val q.val with
  | .handoff => (.handoff s.pc, bank pub s H left elapsed max)
  | .reject => (.reject, bank pub s H left elapsed max)
  | .execute => let prep := TeamOpcode.prepare P pub s
                (.callback prep.1, banks pub prep.2 (chargeRegisters (packed w (H.val-(1+q.val)))
                  (packed w (left.val-(1+q.val))) (packed w (elapsed.val+(1+q.val))) 0)
                  max (wordBits (packed w (elapsed.val+1))))

private theorem after_guard_run (P : TeamOpcode.Program p r k m) (pub : Fin k → Word w)
    (s : TeamOpcode.State w p r) (H left elapsed q max : Word w) (safe : elapsed.val+left.val < 2^w) :
    ∃ t ≤ 1000*(w+1)^2, StackRuns (rows P) t (.check s.pc (.guard (.scan false (.left true))))
      (banks pub s.logged (chargeRegisters H left elapsed q) max []) (.exit (afterGuard P pub s H left elapsed q max).1)
      (afterGuard P pub s H left elapsed q max).2 := by
  obtain ⟨t, ht, hcheck⟩ := check_run P pub s H left elapsed q max
  cases hd : decision H.val left.val q.val with
  | handoff =>
    have hc := installRoutine clearMeter (rows P) (.clear (.handoff s.pc)) _ (fun _ => rfl)
      (clearMeter_runs pub s.logged H left elapsed q 0 max [])
    simp only [hd, checkLabel, reduceCtorEq, ↓reduceIte] at hcheck
    exact ⟨t+2*(8*w+3), by nlinarith [Nat.zero_le (w*w)], by simpa only [afterGuard, hd, bank] using hcheck.trans hc⟩
  | reject =>
    have hc := installRoutine clearMeter (rows P) (.clear .reject) _ (fun _ => rfl)
      (clearMeter_runs pub s.logged H left elapsed q 0 max [])
    simp only [hd, checkLabel, reduceCtorEq, ↓reduceIte] at hcheck
    exact ⟨t+2*(8*w+3), by nlinarith [Nat.zero_le (w*w)], by simpa only [afterGuard, hd, bank] using hcheck.trans hc⟩
  | execute =>
    obtain ⟨tf, hf, finish⟩ := finishCharge_runs pub s.logged H left elapsed q max hd safe
    have hfinish := installRoutine finishCharge (rows P) (.finish s.pc) _ (fun _ => rfl) finish
    obtain ⟨top, ho, hop⟩ := opcode_run P pub s _ max (wordBits (packed w (elapsed.val+1)))
    simp only [hd, checkLabel, ↓reduceIte] at hcheck
    exact ⟨t+tf+top, by nlinarith [Nat.zero_le (w*w)], by simpa only [afterGuard, hd] using (hcheck.trans hfinish).trans hop⟩

/-- Native terminal instructions bypass charging; all other instructions use the pre-fetched
length, and a private call above the read cap is rejected before entering the guard. -/
def result (P : TeamOpcode.Program p r k m) (pub : Fin k → Word w) (s : TeamOpcode.State w p r)
    (H left elapsed max : Word w) : Exit p r m × Stacks (Port r k) :=
  match kind P s.pc with
  | .accept => (.accepted, bank pub s H left elapsed max)
  | .reject => (.reject, bank pub s H left elapsed max)
  | .ordinary => afterGuard P pub s H left elapsed 0 max
  | .burst len => if s.reg len ≤ max then afterGuard P pub s H left elapsed (s.reg len) max
    else (.reject, bank pub s H left elapsed max)

/-- One concrete fixed table guards the whole instruction, stamps its first probe tick
and dispatches it on the actual `ISA.configBank`. Local refusal, over-budget rejection,
and native halt all return their prescribed architecture without executing the opcode. -/
theorem step (P : TeamOpcode.Program p r k m) (pub : Fin k → Word w) (s : TeamOpcode.State w p r)
    (H left elapsed max : Word w) (safe : elapsed.val + left.val < 2^w) :
    ∃ t ≤ 1050*(w+1)^2, StackRuns (rows P) t (.enter s.pc) (bank pub s H left elapsed max)
      (.exit (result P pub s H left elapsed max).1) (result P pub s H left elapsed max).2 := by
  cases hk : kind P s.pc with
  | accept | reject =>
    exact ⟨1, by nlinarith [Nat.zero_le (w*w)], by simp only [result, hk]; exact .cons (.goto (by simp [rows, hk])) (.nil ..)⟩
  | ordinary =>
    obtain ⟨t, ht, hrun⟩ := after_guard_run P pub s H left elapsed 0 max safe
    simp only [result, hk]
    exact ⟨t+1, by nlinarith [Nat.zero_le (w*w)], .cons (.goto (by simp [rows, hk])) hrun⟩
  | burst len =>
    have hs := size_run P pub s H left elapsed max len
    by_cases hb : s.reg len ≤ max
    · rw [ite_eq_left hb] at hs
      obtain ⟨t, ht, run⟩ := after_guard_run P pub s H left elapsed (s.reg len) max safe
      have all := (hs.trans (stage_run P pub s H left elapsed max len)).trans run
      simp only [result, hk, hb, ↓reduceIte]
      exact ⟨8*w+2+(6*w+3)+t+1, by nlinarith [Nat.zero_le (w*w)], .cons (.goto (by simp [rows, hk])) all⟩
    · rw [ite_eq_right hb] at hs
      simp only [result, hk, hb, ↓reduceIte]
      exact ⟨8*w+2+1, by nlinarith [Nat.zero_le (w*w)], .cons (.goto (by simp [rows, hk])) hs⟩

end TeamLocalClock.Loop

end BorderVNP
end Computability
end OAI
