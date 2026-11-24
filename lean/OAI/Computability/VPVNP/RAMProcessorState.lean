import OAI.Computability.VPVNP.RAMProcessorBank
import OAI.Computability.VPVNP.RAMProcessorProbeFields
import Mathlib.Tactic.FinCases

/-!
# The physical bank at call-segment boundaries

This representation names every stack used by the opcode, credit, probe, test,
and record routines. Shared fields occupy a single stack. The same incoming
choices, cost, persistent word, and probe ordinal are therefore visible at each
stage without copying or consulting a global message assignment.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM

variable {w p r k : ℕ}

/-- Place each probe-stage port in the shared site-processor bank, reusing the ISA, choice,
record-field, and running-status stacks and assigning two scratch stacks for copies. -/
def probePorts : ProbeStages.Port r k → Port r k
  | .inl i => .isa i
  | .inr .choices => .test .choices
  | .inr .tag => .record (.field 0)
  | .inr .address => .record (.field 1)
  | .inr .value => .record (.field 2)
  | .inr .running => .test (.bit .running)
  | .inr .copyA => .scratch 0
  | .inr .copyB => .scratch 1

theorem probePorts_injective : Function.Injective (@probePorts r k) := by
  intro i j he
  rcases i with i | a <;> rcases j with j | b
  · exact congrArg Sum.inl (Port.isa.inj he)
  · cases b <;> contradiction
  · cases a <;> contradiction
  · cases a <;> cases b <;> simp_all [probePorts]

/-- The record buffer is already in reverse serialization order. Its
remaining stack contains one mark for each unoccupied slot. -/
structure Snapshot (w p r k : ℕ) where
  /-- Public operand words read by the instruction table during a call. -/
  pub : Fin k → Word w
  /-- Current program counter, persistent word, registers, and private-memory write log of the
  simulated RAM. -/
  cfg : LogConfig w p r
  /-- Public call-cost allowance copied into the call counter when a fresh call begins. -/
  publicH : ℕ
  /-- Public instruction allowance used to reset the fuel of each new call. -/
  publicFuel : ℕ
  /-- Instructions still available to the currently simulated call. -/
  fuel : ℕ
  /-- Remaining units of call cost available under the current call’s allowance. -/
  callLeft : ℕ
  /-- Remaining call-cost units in this site’s budget for its local loop. -/
  siteLeft : ℕ
  /-- Word encoding the upper bound on cumulative call cost for the entire computation. -/
  cap : Word w
  /-- Word holding the remaining global cost credit after charges already incurred. -/
  globalLeft : Word w
  /-- Cumulative cost charged so far, counting one unit per call and one per external probe. -/
  cost : Word w
  /-- Bits of the start-cost field staged for the next record. For a probe this is the
  cumulative cost before its call. -/
  savedStart : List Bool
  /-- Bits encoding the next probe’s zero-based ordinal within the current call. -/
  ordinal : List Bool
  /-- Lower endpoint of the current site’s cost bucket, used to check the incoming running cut. -/
  lower : Word w
  /-- Upper endpoint of the site’s cost bucket. A running computation continues here while its
  cost is below this word. -/
  boundary : Word w
  /-- Cumulative cost advertised by the outgoing successor message for the end-of-site check. -/
  targetCost : Word w
  /-- Persistent word advertised by the outgoing cut when the target is running. -/
  targetState : Word w
  /-- Whether the computation at the current cut has a running persistent state. -/
  running : Bool
  /-- Whether this site has an outgoing successor cut to check at its boundary. -/
  hasTarget : Bool
  /-- Running-status bit of the advertised outgoing cut. -/
  targetRunning : Bool
  /-- Unconsumed private choice bits for RAM branches and guessed external-read answers. -/
  choices : List Bool
  /-- Serialized kind word staged for the current initialization, read, or write record. -/
  tag : List Bool
  /-- Address bits staged for the record that the processor is about to emit. -/
  address : List Bool
  /-- Value bits staged for the initialization, read, or write at the recorded address. -/
  value : List Bool
  /-- One stack marker for each vacant slot in the site’s fixed-capacity record buffer. -/
  remaining : List Bool
  /-- Accumulated serialized record bits in reverse order, ready to be reversed into the output
  block. -/
  reverseBuffer : List Bool
  /-- Stack receiving the padded record block in forward serialization order. -/
  output : List Bool

/-- Expose the public limits, remaining credits, cumulative cost, saved start cost, and probe
ordinal on the credit routine’s ports. -/
def Snapshot.credit (s : Snapshot w p r k) : Stacks CallCredit.Port :=
  CallCredit.bank s.publicH s.publicFuel s.fuel s.callLeft s.siteLeft s.cap s.globalLeft s.cost s.savedStart s.ordinal

/-- Project the bucket endpoints, current cut, outgoing target, status flags, and remaining
choices onto the site-test bank. -/
def Snapshot.tests (s : Snapshot w p r k) : SiteTests.Snapshot w where
  words
    | .lower => s.lower
    | .cost => s.cost
    | .cap => s.cap
    | .state => s.cfg.persistent
    | .boundary => s.boundary
    | .targetCost => s.targetCost
    | .targetState => s.targetState
  flags
    | .running => s.running
    | .hasTarget => s.hasTarget
    | .targetRunning => s.targetRunning
  choices := s.choices

/-- Assemble the ISA bank, choice bits, staged record fields, and running flag used by the
probe handlers. -/
def Snapshot.probe (s : Snapshot w p r k) : ProbeStages.Bank r k where
  isa := ISA.configBank s.pub s.cfg
  choices := s.choices
  tag := s.tag
  address := s.address
  value := s.value
  running := [s.running]

/-- Arrange the five staged record fields, zero padding, vacant-slot markers, and serialization
buffers on the record routine’s ports. -/
def Snapshot.records (s : Snapshot w p r k) : Stacks RecordBuffer.Port
  | .field i => ![s.tag, s.address, s.value, s.savedStart, s.ordinal] i
  | .temp => []
  | .zeros => List.replicate w false
  | .remaining => s.remaining
  | .reverseBuffer => s.reverseBuffer
  | .output => s.output

/-- Unused copies of aliased port labels stay blank. -/
def Snapshot.bank (s : Snapshot w p r k) : Stacks (Port r k)
  | .isa i => ISA.configBank s.pub s.cfg i
  | .credit i => s.credit i
  | .test (.word .cost) | .test (.word .cap) | .test (.word .state) => []
  | .test i => s.tests.bank i
  | .record (.field i) => if i = 3 ∨ i = 4 then [] else s.records (.field i)
  | .record i => s.records i
  | .scratch _ => []

theorem Snapshot.local_at (s : Snapshot w p r k) (j : LocalProcessor.Port r k) :
    s.bank (localPorts j) = LocalProcessor.store s.pub s.cfg s.fuel s.choices j := by
  rcases j with j | b
  · rfl
  · cases b <;> rfl

theorem Snapshot.test_at (s : Snapshot w p r k) (j : SiteTests.Port) :
    s.bank (testPorts j) = s.tests.bank j := by
  cases j with
  | word f => cases f <;> rfl
  | _ => rfl

theorem Snapshot.probe_at (s : Snapshot w p r k) (j : ProbeStages.Port r k) :
    s.bank (probePorts j) = s.probe.stacks j := by
  rcases j with j | j
  · rfl
  · cases j <;> rfl

theorem Snapshot.record_at (s : Snapshot w p r k) (j : RecordBuffer.Port) :
    s.bank (recordPorts j) = s.records j := by
  cases j with
  | field i => fin_cases i <;> rfl
  | _ => rfl

/-- Install the configuration, remaining fuel, and unused choice bits yielded by a local
instruction segment. -/
def Snapshot.afterLocal (s : Snapshot w p r k) (y : LocalProcessor.Yield w p r) : Snapshot w p r k :=
  {s with cfg := y.cfg, fuel := y.fuel, choices := y.bits}

/-- A local segment changes only its ISA bank, remaining fuel, and choices. -/
theorem Snapshot.installLocal (s : Snapshot w p r k) (y : LocalProcessor.Yield w p r) :
    installStacks localPorts s.bank (LocalProcessor.store s.pub y.cfg y.fuel y.bits) =
      (s.afterLocal y).bank := by
  apply installStacks_frame localPorts_injective
  · exact (s.afterLocal y).local_at
  · intro j hj
    cases j with
    | isa i => exact (hj (.inl i) rfl).elim
    | credit i =>
      cases i with
      | budget i => cases i <;> first | rfl | exact (hj (.inr false) rfl).elim
      | _ => rfl
    | test i =>
      cases i with
      | choices => exact (hj (.inr true) rfl).elim
      | word f => cases f <;> rfl
      | _ => rfl
    | record i => cases i <;> rfl
    | scratch _ => rfl

theorem Snapshot.runLocal (s : Snapshot w p r k) (T : Template p r k) (limit : ℕ)
    (hl : s.cfg.writes.length+s.fuel ≤ limit) :
    let y := LocalProcessor.scan T s.pub s.fuel s.cfg s.choices
    ∃ t ≤ s.fuel*(ISA.prepareBound w limit+4)+1,
      (localBlock T s.cfg.pc).Runs t s.bank y.exit (s.afterLocal y).bank := by
  obtain ⟨t, ht, run⟩ := localBlock_run T s.pub s.fuel s.cfg s.choices limit hl s.bank s.local_at
  exact ⟨t, ht, s.installLocal _ ▸ run⟩

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
