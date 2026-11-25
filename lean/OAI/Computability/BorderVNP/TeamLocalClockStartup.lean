import OAI.Computability.BorderVNP.TeamLocalClockStartupLayout

/-!
# Entering the clocked processor from its physical successor link

The receiver decodes into the ISA and clock registers, reconstructs its finite
instruction label and initializes its remaining global budget. A prior accepted
halt checks its elapsed time before propagating. Processor zero enters at its
public instruction label
with the canonical time-zero architecture.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamLocalClock.Startup

open VPVNP RAMTape BurstRAM TeamTapeHandoff RAMTape.PublicExprMachine
open TeamLocalClockPC (Outcome)

variable {p r k w : ℕ}

/-- Fixed entry labels for processor zero, the incident decoder, PC lookup and clock guard. -/
inductive State (p r : ℕ) where
  | first (pc : Fin p) | decode (q : (Codec.decode r).State)
  | lookup (q : TeamLocalClockPC.State p) | clock (pc : Fin p) (q : StartupState)
  | haltClock (q : SuccessorCap.State) | done (result : Outcome p)
  deriving Fintype

private def afterDecode : Option (Codec.decode r).State → State p r
  | some q => .decode q
  | none => .lookup .status

private def afterLookup : TeamLocalClockPC.State p → State p r
  | .done (.live pc) => .clock pc (.scan (.left true))
  | .done .accepted => .haltClock (.left true)
  | .done .reject => .done .reject
  | q => .lookup q

private def afterClock (pc : Fin p) : StartupState → State p r
  | .done ok => .done (if ok then .live pc else .reject)
  | q => .clock pc q

private abbrev pcPorts : TeamLocalClockPC.Port → Port r k :=
  codecPorts ∘ TeamLocalClockPC.framePorts

private abbrev meterPorts : ISA.Port 6 0 → Port r k := Port.clock ∘ TeamLocalClock.Port.meter

private def haltPorts : TapeWord.ScanPort → Port r k
  | .left => meterPorts (.reg 2)
  | .right => meterPorts (.reg 1)
  | .tmp => meterPorts (.work 0)
  | .out => meterPorts (.work 1)

private theorem haltPorts_injective : Function.Injective (@haltPorts r k) := by
  intro x y h
  cases x <;> cases y <;> simp_all [haltPorts, meterPorts]

private def afterHaltClock : SuccessorCap.State → State p r
  | .done ok => .done (if ok then .accepted else .reject)
  | q => .haltClock q

/-- The fixed control for starting a processor. Runtime width, clock budgets and the incoming
PC do not enter its instruction table. The outgoing terminal is available to a caller. -/
def code (p r k : ℕ) : StackCode (Port r k) (State p r)
  | .first pc => .goto (.done (.live pc))
  | .decode q => ((Codec.decode r).body.code q).rename codecPorts afterDecode
  | .lookup q => (TeamLocalClockPC.code p q).rename pcPorts afterLookup
  | .clock pc q => (startupCode q).rename meterPorts (afterClock pc)
  | .haltClock q => (SuccessorCap.code q).rename haltPorts afterHaltClock
  | .done .reject => .halt false
  | .done _ => .halt true

/-- Start of the noninitial processor's incident-message decoder. -/
def entry (p r : ℕ) : State p r := .decode (Codec.decode r).body.entry

private theorem decode_run (pub : Fin k → Word w) (f : Frame w r) (H limit max : Word w)
    (suffix : List Bool) :
    StackRuns (code p r k) ((r + 2) * (6 * w + 2) + 3) (entry p r)
      (input pub H limit max (f.bits ++ suffix)) (.lookup .status)
      (decoded pub f H limit max suffix) := by
  let start := input (r := r) pub H limit max (f.bits ++ suffix)
  have h := (Codec.decode_runs f suffix).lift (target := code p r k) codecPorts
    codecPorts_injective afterDecode start (fun q hh => by cases q <;> first | rfl | contradiction)
  have eq := installStacks_eq codecPorts_injective start (Codec.incoming r w (f.bits ++ suffix))
    (fun u => installStacks_at codecPorts_injective _ _ u)
  rw [eq, decoded_install] at h
  exact h

private theorem pcRows (q : TeamLocalClockPC.State p)
    (hq : (TeamLocalClockPC.code p q).returns = false) :
    code p r k (afterLookup q) = (TeamLocalClockPC.code p q).rename pcPorts afterLookup := by
  cases q with
  | done o => cases o <;> contradiction
  | _ => rfl

private theorem lookup_run (pub : Fin k → Word w) (pcWord elapsed : Word w)
    (regs : Fin r → Word w) (H limit max : Word w) (suffix : List Bool) :
    let f := Frame.live pcWord regs elapsed
    let s := decoded pub f H limit max suffix
    StackRuns (code p r k) (4 * w + 4) (.lookup .status) s
      (afterLookup (.done (TeamLocalClockPC.lookup p pcWord.val))) s := by
  intro f s
  let ports : TeamLocalClockPC.Port → Port r k := pcPorts
  have inj : Function.Injective ports :=
    codecPorts_injective.comp TeamLocalClockPC.framePorts_injective
  have ht (i) : s (ports i) = Codec.bank f suffix (TeamLocalClockPC.framePorts i) :=
    decoded_codec pub f H limit max suffix _
  have hs := TeamLocalClockPC.live_run p (s ∘ ports) [] (ht .tag) (ht .tmp)
  have lifted := hs.lift ports inj afterLookup s pcRows
  rw [installStacks_eq inj s (s ∘ ports) (fun _ => rfl)] at lifted
  have hp : (s ∘ ports) .pc = wordBits pcWord := (ht .pc).trans rfl
  rw [hp, length_wordBits, TapeWord.value_wordBits] at lifted
  exact lifted

private theorem clock_run (pub : Fin k → Word w) (f : Frame w r) (pc : Fin p)
    (H limit max : Word w) (suffix : List Bool) :
    ∃ t ≤ 8 * w + 2 + 150 * (w + 1) ^ 2,
      StackRuns (code p r k) t (.clock pc (.scan (.left true))) (decoded pub f H limit max suffix)
        (.done (if f.elapsed ≤ limit then .live pc else .reject))
        (decoded pub f H (if f.elapsed ≤ limit then packed w (limit.val - f.elapsed.val)
          else limit) max suffix) := by
  obtain ⟨t, ht, hr⟩ := startup_run H limit f.elapsed 0 (0 : Word w) []
  let s := decoded pub f H limit max suffix
  have inj : Function.Injective (@meterPorts r k) :=
    fun _ _ he => TeamLocalClock.Port.meter.inj (Port.clock.inj he)
  have lifted := hr.lift (target := code p r k) meterPorts inj (afterClock pc) s
    (fun q h => by cases q <;> first | rfl | contradiction)
  have he := installStacks_eq inj s
    (ISA.bank Fin.elim0 0 (startupRegisters H limit f.elapsed 0) []) (fun _ => rfl)
  rw [he] at lifted
  refine ⟨t, ht, ?_⟩
  by_cases h : f.elapsed ≤ limit <;>
    simpa only [s, h, decide_true, decide_false, afterClock, startupRegisters, Bool.false_eq_true,
      ite_false, ite_true, meter_install] using lifted

/-- The actual checked predecessor's words initialize both register banks. A valid program label
is recovered exactly, and clock overruns reject before the first opcode. -/
theorem live_run (pub : Fin k → Word w) (pc : Fin p) (fits : p ≤ 2 ^ w)
    (regs : Fin r → Word w) (H limit elapsed max : Word w) (suffix : List Bool) :
    let f := Frame.live (packed w pc.val) regs elapsed
    ∃ t ≤ (r + 2) * (6 * w + 2) + 3 + (4 * w + 4) + (8 * w + 2 + 150 * (w + 1) ^ 2),
      StackRuns (code p r k) t (entry p r) (input pub H limit max (f.bits ++ suffix))
        (.done (if elapsed ≤ limit then .live pc else .reject))
        (decoded pub f H (if elapsed ≤ limit then packed w (limit.val - elapsed.val)
          else limit) max suffix) := by
  intro f
  have first := decode_run (p := p) pub f H limit max suffix
  have second := lookup_run (p := p) pub (packed w pc.val) elapsed regs H limit max suffix
  dsimp only at second
  rw [TeamLocalClockPC.lookup_packed pc fits] at second
  obtain ⟨t, ht, last⟩ := clock_run pub f pc H limit max suffix
  exact ⟨_, by omega, (first.trans second).trans last⟩

/-- A live wire PC outside the finite instruction table rejects without changing the incoming
fields, even if the word encoding itself is otherwise well formed. -/
theorem invalidPC_run (pub : Fin k → Word w) (pcWord elapsed : Word w) (regs : Fin r → Word w)
    (H limit max : Word w) (suffix : List Bool) (invalid : p ≤ pcWord.val) :
    let f := Frame.live pcWord regs elapsed
    StackRuns (code p r k) ((r + 2) * (6 * w + 2) + 3 + (4 * w + 4)) (entry p r)
      (input pub H limit max (f.bits ++ suffix)) (.done .reject)
      (decoded pub f H limit max suffix) := by
  intro f
  have second := lookup_run (p := p) pub pcWord elapsed regs H limit max suffix
  dsimp only at second
  rw [(TeamLocalClockPC.lookup_reject_iff ..).mpr invalid] at second
  exact (decode_run pub f H limit max suffix).trans second

/-- A canonical accepted frame propagates exactly when its elapsed tick fits the
public cap. This comparison restores all operands and leaves the suffix intact. -/
theorem halted_run (p : ℕ) (pub : Fin k → Word w) (H limit elapsed max : Word w)
    (suffix : List Bool) :
    let f : Frame w r := .accepted elapsed
    StackRuns (code p r k) ((r + 2) * (6 * w + 2) + 3 + 2 + (8 * w + 2)) (entry p r)
      (input pub H limit max (f.bits ++ suffix))
      (.done (if elapsed ≤ limit then .accepted else .reject))
      (decoded pub f H limit max suffix) := by
  intro f
  let s := decoded pub f H limit max suffix
  have h := TeamLocalClockPC.halted_run p (s ∘ pcPorts) []
    (decoded_codec pub f H limit max suffix .tag)
  have inj : Function.Injective (@pcPorts r k) :=
    codecPorts_injective.comp TeamLocalClockPC.framePorts_injective
  have last := h.lift pcPorts inj afterLookup s pcRows
  rw [installStacks_eq inj s (s ∘ pcPorts) (fun _ => rfl)] at last
  have guard := SuccessorCap.run_lift haltPorts haltPorts_injective
    (target := code p r k) afterHaltClock
    (by intro q hq; cases q <;> first | rfl | contradiction) s
    (show (wordBits elapsed).length = (wordBits limit).length by simp) rfl rfl
  change StackRuns _ (8 * (wordBits elapsed).length + 2) _ _
    (afterHaltClock (.done (decide (TapeWord.value (wordBits elapsed) ≤
      TapeWord.value (wordBits limit))))) _ at guard
  simp only [length_wordBits, TapeWord.value_wordBits, afterHaltClock, decide_eq_true_eq] at guard
  exact ((decode_run pub f H limit max suffix).trans last).trans guard

/-- Processor zero starts at the public label with the canonical initial register frame, zero
elapsed ticks and full global budget. It has no predecessor wire to read. -/
theorem first_run (pub : Fin k → Word w) (pc : Fin p) (regs : Fin r → Word w)
    (H limit max : Word w) (suffix : List Bool) :
    let f := initial (packed w pc.val) regs
    let s := decoded pub f H limit max suffix
    StackRuns (code p r k) 1 (.first pc) s (.done (.live pc)) s :=
  .cons (.goto rfl) (.nil ..)

end TeamLocalClock.Startup

end BorderVNP
end Computability
end OAI
