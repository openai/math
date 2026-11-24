import OAI.Computability.VPVNP.RAMProcessorLocalResult
import OAI.Computability.VPVNP.RAMProcessorCallCredit
import OAI.Computability.VPVNP.RAMProcessorSiteTests
import OAI.Computability.VPVNP.RAMTapeRecordBuffer

/-!
# Shared stack bank of the physical burst-site controller

The instruction interpreter and credit routines read the same fuel tally.
The site tests read the same cost and persistent state as the call controller.
Record fields three and four directly name the saved start cost and current
probe ordinal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM

/-- Stacks of the physical site controller for instruction execution, credit accounting, tests,
record emission and temporary work. -/
inductive Port (r k : ℕ) where
  | isa (i : ISA.Port r k)
  | credit (i : CallCredit.Port)
  | test (i : SiteTests.Port)
  | record (i : RecordBuffer.Port)
  | scratch (i : Fin 8)
  deriving DecidableEq, Fintype

variable {r k p w : ℕ}

/-- Embed the local instruction processor, sharing its fuel stack with the credit bank and its
choice stream with the site tests. -/
def localPorts : LocalProcessor.Port r k → Port r k
  | .inl i => .isa i
  | .inr false => .credit (.budget .fuel)
  | .inr true => .test .choices

theorem localPorts_injective : Function.Injective (@localPorts r k) := by
  intro i j h
  rcases i with i | b <;> rcases j with j | c
  · exact congrArg Sum.inl (Port.isa.inj h)
  · cases c <;> contradiction
  · cases b <;> contradiction
  · cases b <;> cases c <;> first | rfl | contradiction

/-- Route the cost and cap tests to the credit bank and the state test to the persistent ISA
word, with the other tests on their dedicated ports. -/
def testPorts : SiteTests.Port → Port r k
  | .word .cost => .credit (.budget .cost)
  | .word .cap => .credit .globalCap
  | .word .state => .isa .persistent
  | i => .test i

theorem testPorts_injective : Function.Injective (@testPorts r k) := by
  let back : Port r k → SiteTests.Port
    | .credit (.budget .cost) => .word .cost
    | .credit .globalCap => .word .cap
    | .isa .persistent => .word .state
    | .test i => i
    | _ => .choices
  apply Function.LeftInverse.injective (g := back)
  intro i
  cases i with
  | word f => cases f <;> rfl
  | _ => rfl

/-- Route the record's starting cost and probe ordinal to their live credit stacks and its
other fields to the record buffer. -/
def recordPorts : RecordBuffer.Port → Port r k
  | .field i => if i = 3 then .credit .savedStart else if i = 4 then .credit .ordinal else .record (.field i)
  | i => .record i

theorem recordPorts_injective : Function.Injective (@recordPorts r k) := by
  let back : Port r k → RecordBuffer.Port
    | .credit .savedStart => .field 3
    | .credit .ordinal => .field 4
    | .record i => i
    | _ => .temp
  apply Function.LeftInverse.injective (g := back)
  intro i
  cases i with
  | field j => by_cases hj : j = 3 <;> by_cases hk : j = 4 <;> simp_all [recordPorts, back]
  | _ => rfl

private def localExit (T : Template p r k) : LocalProcessor.State T → Option (ISA.Callback p r)
  | .exit cb => some cb
  | _ => none

/-- One call segment performs the actual instruction fetches and stops on its
external-action label, with private choice bits and fuel updated in the bank. -/
def localBlock (T : Template p r k) (pc : Fin p) : Fragment (Port r k) (ISA.Callback p r) :=
  (Fragment.fromCode (LocalProcessor.code T) (.begin pc) (localExit T)).onPorts localPorts

theorem localBlock_run (T : Template p r k) (pub : Fin k → Word w) (f : ℕ)
    (c : LogConfig w p r) (bs : List Bool) (limit : ℕ) (hl : c.writes.length+f ≤ limit)
    (s : Stacks (Port r k)) (hs : ∀ j, s (localPorts j) = LocalProcessor.store pub c f bs j) :
    let out := LocalProcessor.scan T pub f c bs
    ∃ t ≤ f*(ISA.prepareBound w limit+4)+1,
      (localBlock T c.pc).Runs t s out.exit
        (installStacks localPorts s (LocalProcessor.store pub out.cfg out.fuel out.bits)) := by
  obtain ⟨t, ht, run⟩ := LocalProcessor.scan_run T pub f c bs limit hl
  have core := Fragment.fromCode_runs (localExit T) rfl rfl
    (fun q h => by cases q <;> first | rfl | contradiction) run
  have h := Fragment.runs_onPorts localPorts localPorts_injective s core
  rw [installStacks_eq localPorts_injective s _ hs] at h
  exact ⟨t, ht, h⟩

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
