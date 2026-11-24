import OAI.Computability.VPVNP.RAMTapeProcessorStartup
import OAI.Computability.VPVNP.RAMTapeSuccessorTotal
import OAI.Computability.VPVNP.RAMTapeSuccessorCuts
import OAI.Computability.VPVNP.RAMTapeRoutineTotalPorts
import OAI.Computability.VPVNP.EvaluatorRoutineFrame

/-!
# The successor guard on the actual public processor bank

The reader addresses the parsed site and incident bits, the computed word width and cap,
and the literal initial word directly in the public bank. Its running flags, decoded words
and record payloads occupy separate auxiliary stacks. The guarded output below is the exact
stack state supplied to the call loop or sorting pass on a valid pair of successor fields.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteCutBank
set_option synthInstance.maxSize 256

open BurstRAM ProcessorInput RAMLayout

/-- Auxiliary guard ports for outgoing presence, per-side status, endpoint records, and eight
decoded words on each side. -/
inductive Aux where
  | outPresent | running (side : Successors.Side) | verdict (side : Successors.Side)
  | record (side : Successors.Side) | word (side : Successors.Side) (i : Fin 8)
  deriving DecidableEq, Fintype

/-- Combined public processor and successor-guard auxiliary bank. -/
abbrev Port := ProcessorPublic.Port ⊕ Aux

/-- Connect the successor reader to the parsed public fields and its dedicated scratch,
decoded-word, and endpoint-record ports. -/
def ports : Successors.Port → Port
  | .address => .inl ProcessorPublic.addressPort
  | .incident => .inl ProcessorPublic.incidentPort
  | .width => .inl ProcessorPublic.widthPort
  | .cap => .inl ProcessorPublic.capPort
  | .initial => .inl ProcessorPublic.initPort
  | .tmp => .inl (.inr (.scratch 0))
  | .capTmp => .inl (.inr (.scratch 1))
  | .outPresent => .inr .outPresent
  | .running side => .inr (.running side)
  | .verdict side => .inr (.verdict side)
  | .record side => .inr (.record side)
  | .word side i => .inr (.word side i)

theorem ports_injective : Function.Injective ports := by decide

/-- Run the two successor-field checks directly on the processor and guard banks. -/
def checked : FiniteRoutine Port := Successors.checked.onPorts ports

/-- Site data and width bounds used by the shared-bit guard. -/
structure Input (d e w : ℕ) where
  /-- Universal program whose literal prefix appears in the site input. -/
  prog : UniversalMachine.Program
  /-- Length of the complete physical site input, including its padding. -/
  n : ℕ
  /-- Exponent giving the private instruction allowance as a power of the input length. -/
  u : ℕ
  /-- Natural literal loaded as the private computation’s initial state word. -/
  lit : ℕ
  /-- Site address encoded in the public address width. -/
  v : Word d
  /-- Four-bit header accompanying the site address on the input. -/
  hdr : Header
  /-- Shared send arrays that determine the site’s incident bits and successor checks. -/
  sends : SendArrays d (2^e) w
  hcap : d + e < w
  hw : 4 ≤ w
  width_eq : w = (d+10)^4

variable {d e w : ℕ} (x : Input d e w)

include x in
theorem Input.cap_lt : 2^d * 2^e < 2^w := (SuccessorParameters.capWord d e w x.hcap).isLt

include x in
theorem Input.word_ge_two : 2 ≤ w := (by decide : 2 ≤ 4).trans x.hw

/-- Initial-state literal packed into a word of the site’s RAM width. -/
def Input.initialWord : Word w := Fin.ofNat (2^w) x.lit

/-- The public half is exactly the output of `recordStartup_runs`. -/
def Input.prepared : Stacks Port := Sum.elim (ProcessorPublic.recordResult
  (ProcessorPublic.rawResult x.prog x.n d (2^e) w x.v x.hdr (incidentBits x.sends x.v))
  x.n d e w x.u x.lit x.v x.hdr x.hcap x.hw) (fun _ => [])

theorem Input.width_ready : (x.prepared ∘ ports) .width = List.replicate w true := by
  conv_rhs => rw [x.width_eq]
  rfl

/-- Both the sent and received successor fields satisfy their respective checks at the selected
site. -/
def Input.valid : Prop := SuccessorSendOK x.word_ge_two x.cap_lt x.sends x.v ∧
  SuccessorReceiveOK x.word_ge_two x.cap_lt x.sends x.v

/-- Actual continuation bank. Every update is local to the named guard ports. -/
noncomputable def Input.guarded : Stacks Port := installStacks ports x.prepared
  (Successors.guardResult (Successors.sharedFinish x.cap_lt x.sends x.v (x.prepared ∘ ports)))

@[simp] theorem guarded_at (p : Successors.Port) :
    x.guarded (ports p) = Successors.guardResult
      (Successors.sharedFinish x.cap_lt x.sends x.v (x.prepared ∘ ports)) p :=
  installStacks_at ports_injective _ _ p

theorem guarded_outside (i : Port) (h : ∀ p, ports p ≠ i) : x.guarded i = x.prepared i :=
  installStacks_outside _ _ h

/-- Step count of the successor-field scan, with predecessor presence determined by whether the
site address is positive. -/
def Input.readSteps : ℕ := Successors.steps d w (decide (0 < x.v.val))

open scoped Classical in
/-- Rejection contributes zero. A valid pair reaches the continuation once, after two guard pops. -/
theorem checked_count (c : ℕ → Stacks Port → ℕ) (fuel : ℕ) :
    checked.body.count c (fuel + 2 + x.readSteps) x.prepared =
      if x.valid then c fuel x.guarded else 0 := by
  rw [checked, FiniteRoutine.count_onPorts _ _ ports_injective]
  have h := Successors.checked_shared_count x.word_ge_two x.cap_lt x.sends (x.prepared ∘ ports) x.v x.initialWord
    rfl rfl x.width_ready rfl rfl rfl rfl (fun _ _ => rfl)
    (fun f out => c f (installStacks ports x.prepared out)) fuel
  dsimp only at h
  by_cases hgood : x.valid
  · rw [ite_eq_left hgood, ite_eq_left (show SuccessorSendOK _ _ _ _ ∧ SuccessorReceiveOK _ _ _ _ from hgood)] at *
    exact h
  · rw [ite_eq_right hgood, ite_eq_right (show ¬ (SuccessorSendOK _ _ _ _ ∧ SuccessorReceiveOK _ _ _ _) from hgood)] at *
    exact h

/-- Three guard ticks suffice for either rejection path. On a valid pair the extra tick
is passed to the continuation. -/
theorem checked_allStops (c : ℕ → Stacks Port → Prop) (fuel : ℕ) :
    checked.body.AllStops c (fuel + 3 + x.readSteps) x.prepared ↔
      (x.valid → c (fuel + 1) x.guarded) := by
  rw [checked, FiniteRoutine.allStops_onPorts _ _ ports_injective]
  exact Successors.checked_shared_allStops x.word_ge_two x.cap_lt x.sends (x.prepared ∘ ports) x.v x.initialWord
    rfl rfl x.width_ready rfl rfl rfl rfl (fun _ _ => rfl) _ fuel

theorem checked_runs (h : x.valid) : checked.Runs (x.readSteps + 2) x.prepared x.guarded := by
  have localRun := Successors.checked_shared_runs x.word_ge_two x.cap_lt x.sends
    (x.prepared ∘ ports) x.v x.initialWord rfl rfl x.width_ready rfl rfl rfl rfl (fun _ _ => rfl) h
  have run := Successors.checked.runs_onPorts ports_injective x.prepared localRun
  rwa [installStacks_eq ports_injective x.prepared (x.prepared ∘ ports) (fun _ => rfl)] at run

/-- Cost, state, record, presence and remaining incident bits at the guard's normal return. -/
theorem guarded_registers (h : x.valid) :
    Successors.CutRegisters (x.prepared ∘ ports) (x.guarded ∘ ports) x.word_ge_two
      (scanSuccessors x.word_ge_two x.cap_lt x.initialWord x.v (sortIncident x.sends x.v)).1
      ((List.ofFn (incidentBits x.sends x.v)).drop (16*w)) := by
  have hout : x.guarded ∘ ports = Successors.guardResult
      (Successors.sharedFinish x.cap_lt x.sends x.v (x.prepared ∘ ports)) := funext (guarded_at x)
  rw [hout]
  exact Successors.guarded_cutRegisters x.word_ge_two x.cap_lt x.initialWord x.sends x.v
    (x.prepared ∘ ports) rfl h.1 h.2

end RAMTape.SiteCutBank

end VPVNP
end Computability
end OAI
