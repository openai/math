import OAI.Computability.BorderVNP.TeamBurstCallbackSetup
import OAI.Computability.BorderVNP.TeamLink

/-! # Installing the guarded variable-length burst callback

A single finite control starts with the four live RAM operands, prepares the sorter and
guess scratch, checks the address-space and cap inequalities, and enters the physical
consecutive-probe loop. A failed check reaches a literal rejecting halt before any
choice is made. All links preserve the caller's unaddressed stacks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamBurstCallback

open VPVNP BurstRAM RAMTape RAMSerialization
open TeamBurstCallbackSetup (Port Ready)

/-- Labels of the physical setup, range check and probe loop. The selected source registers
are fixed by the RAM instruction's two literal register indices. -/
inductive State {r : ℕ} (addr len : Fin r)
  | setup (z : (TeamBurstCallbackSetup.program addr len).State)
  | entry (z : TeamBurstEntry.program.State)
  | loop (z : TeamBurstProbe.LoopState)
  deriving Fintype

/-- Initial setup control of a fixed burst instruction. -/
def start {r : ℕ} (addr len : Fin r) : State addr len :=
  .setup (TeamBurstCallbackSetup.program addr len).body.entry

/-- Install all callback rows. A normal setup return enters the guard, a normal guard
return enters the loop, and the loop finishes at the supplied private-machine entry. -/
def rows {r : ℕ} {K R : Type} (addr len : Fin r) (ports : Port r → K)
    (label : State addr len → R) (resume : R) : State addr len → StackOp K R
  | .setup z => ((TeamBurstCallbackSetup.program addr len).body.code z).rename ports
      (Option.elim · (label (.entry TeamBurstEntry.program.body.entry)) (label ∘ State.setup))
  | .entry z => (TeamBurstEntry.program.body.code z).rename (ports ∘ TeamBurstCallbackSetup.entryPorts)
      (Option.elim · (label (.loop .test)) (label ∘ State.entry))
  | .loop z => TeamBurstProbe.rows (ports ∘ Port.step) (label ∘ State.loop) resume z

/-- Caller bank at the first loop test, with the fresh private input and the unary countdown. -/
def initialized {r : ℕ} (addr len : Fin r) (s : Stacks (Port r)) (q : ℕ) : Stacks (Port r) :=
  Function.update (TeamBurstCallbackSetup.prepared addr len s) (.step .marks) (List.replicate q true)

/-- Uniform cost bound for a successful deterministic prefix. -/
def entryCost (w q : ℕ) : ℕ := 60*(w+1) + (7*q+29*w+13)

/-- The last instruction counted in this bound reaches the rejecting halt label. -/
def rejectCost (w : ℕ) : ℕ := 60*(w+1) + (18*w+9)

/-- Reinsert a complete probe bank, retaining the caller's registers and guard scratch. -/
def withStep {r : ℕ} (s : Stacks (Port r)) (u : Stacks TeamBurstProbeStep.Port) : Stacks (Port r)
  | .step j => u j
  | j => s j

/-- Framing a probe run in its callback and then in an enclosing machine agrees with
framing it directly in the enclosing machine. -/
theorem mount_step {r : ℕ} {K : Type} (ports : Port r → K) (hp : Function.Injective ports)
    (base : Stacks K) (s : Stacks (Port r)) (u : Stacks TeamBurstProbeStep.Port) :
    installStacks (ports ∘ Port.step) (installStacks ports base s) u =
      installStacks ports base (withStep s u) := by
  apply installStacks_frame (hp.comp (fun _ _ h => Port.step.inj h))
  · intro j
    exact installStacks_at hp base (withStep s u) (.step j)
  · intro k hk
    by_cases h : ∃ j, ports j = k
    · obtain ⟨j,rfl⟩ := h
      rw [installStacks_at hp, installStacks_at hp]
      cases j with
      | step j => exact (hk j rfl).elim
      | _ => rfl
    · rw [installStacks_outside _ _ (not_exists.mp h), installStacks_outside _ _ (not_exists.mp h)]

variable {r w H : ℕ} {hw : 2 ≤ w+1} {addr len : Fin r} {a q tick cap : Word w}
variable {rs : List (WordRecord (w+1))} {s : Stacks (Port r)}

/-- The setup and guard leave exactly the ready bank required by the installed loop. -/
theorem ready_loop (ready : Ready hw H addr len a q tick cap rs s) :
    TeamBurstProbe.LoopReady hw H a tick rs [] q.val ((initialized addr len s q.val) ∘ Port.step) := by
  have first := TeamBurstCallbackSetup.loop_ready ready
  refine ⟨⟨first.step.address, first.step.time, first.step.before, first.step.after, first.step.bytes,
    first.step.scratch, ?_, ?_, ?_⟩, ?_, first.width, first.saved, first.input⟩
  · exact first.step.lifted
  · exact first.step.buffer
  · exact first.step.fields
  · simp [initialized, Function.comp_apply]

variable {K R : Type} [DecidableEq K]

omit [DecidableEq K] in
/-- A guard bank is the restriction of the full callback bank to the guard's physical ports. -/
private theorem mount_eq (ports : Port r → K) (hp : Function.Injective ports) (base : Stacks K)
    (u : Stacks (Port r)) :
    installStacks (ports ∘ TeamBurstCallbackSetup.entryPorts) (installStacks ports base u)
      (u ∘ TeamBurstCallbackSetup.entryPorts) = installStacks ports base u :=
  installStacks_eq (hp.comp TeamBurstCallbackSetup.entryPorts_injective) _ _ fun _ =>
    installStacks_at hp ..

/-- The valid callback deterministically reaches the first probe test on the real bank.
The two source registers may alias. -/
theorem start_valid (target : StackCode K R) (ports : Port r → K) (hp : Function.Injective ports)
    (label : State addr len → R) (resume : R)
    (hr : ∀ z, target (label z) = rows addr len ports label resume z) (base : Stacks K)
    (ready : Ready hw H addr len a q tick cap rs s) (legal : q.val ≤ cap.val ∧ a.val+q.val ≤ 2^w) :
    ∃ n ≤ entryCost w q.val, StackRuns target n (label (start addr len)) (installStacks ports base s)
      (label (.loop .test)) (installStacks ports base (initialized addr len s q.val)) := by
  let u := TeamBurstCallbackSetup.prepared addr len s
  let m := TeamBurstCallbackSetup.entryPorts (r := r)
  obtain ⟨k,hk,rk⟩ := TeamBurstCallbackSetup.runs addr len ready
  have r₁ := TeamLink.routine rk target ports hp (label ∘ State.setup)
    (label (.entry TeamBurstEntry.program.body.entry)) base fun z => hr (.setup z)
  obtain ⟨j,hj,rj⟩ := TeamBurstEntry.runs (TeamBurstCallbackSetup.entry_ready ready) legal
  have inj := hp.comp (TeamBurstCallbackSetup.entryPorts_injective (r := r))
  have r₂ := TeamLink.routine rj target (ports ∘ m) inj (label ∘ State.entry) (label (.loop .test))
    (installStacks ports base u) fun z => hr (.entry z)
  have same := mount_eq ports hp base u
  change installStacks (ports ∘ m) (installStacks ports base u) (u ∘ m) = installStacks ports base u at same
  change StackRuns target j _ (installStacks (ports ∘ m) (installStacks ports base u) (u ∘ m)) _
    (installStacks (ports ∘ m) (installStacks ports base u) (TeamBurstEntry.prepared (u ∘ m) q.val)) at r₂
  rw [TeamBurstEntry.prepared, ← installStacks_update inj, same] at r₂
  change StackRuns target j _ (installStacks ports base u) _
    (Function.update (installStacks ports base u) (ports (.step .marks)) (List.replicate q.val true)) at r₂
  rw [installStacks_update hp] at r₂
  exact ⟨_, Nat.add_le_add hk hj, r₁.trans r₂⟩

/-- A failed guard reaches an actual rejecting row in the enclosing machine without
consuming a choice or entering the word-guess loop. -/
theorem start_invalid_label (target : StackCode K R) (ports : Port r → K) (hp : Function.Injective ports)
    (label : State addr len → R) (resume : R)
    (hr : ∀ z, target (label z) = rows addr len ports label resume z) (base : Stacks K)
    (ready : Ready hw H addr len a q tick cap rs s) (bad : ¬ (q.val ≤ cap.val ∧ a.val+q.val ≤ 2^w)) :
    ∃ n ≤ rejectCost w, ∃ bank, StackRuns target n (label (start addr len)) (installStacks ports base s)
      (label (.entry TeamBurstEntry.rejection)) bank ∧ target (label (.entry TeamBurstEntry.rejection)) = .halt false := by
  let u := TeamBurstCallbackSetup.prepared addr len s
  let m := TeamBurstCallbackSetup.entryPorts (r := r)
  let toState (z : Option TeamBurstEntry.program.State) : R :=
    z.elim (label (.loop .test)) (label ∘ State.entry)
  obtain ⟨k,hk,rk⟩ := TeamBurstCallbackSetup.runs addr len ready
  have r₁ := TeamLink.routine rk target ports hp (label ∘ State.setup)
    (label (.entry TeamBurstEntry.program.body.entry)) base fun z => hr (.setup z)
  have rj := TeamBurstEntry.invalid_runs (TeamBurstCallbackSetup.entry_ready ready) bad
  have r₂ := rj.lift (target := target) (ports ∘ m) (hp.comp TeamBurstCallbackSetup.entryPorts_injective)
    toState (installStacks ports base u) (by
      rintro (_ | z) h
      · contradiction
      · exact hr (.entry z))
  change StackRuns target (18*w+9) (label (.entry TeamBurstEntry.program.body.entry))
    (installStacks (ports ∘ m) (installStacks ports base u) (u ∘ m))
    (label (.entry TeamBurstEntry.rejection))
    (installStacks (ports ∘ m) (installStacks ports base u) (u ∘ m)) at r₂
  have same := mount_eq ports hp base u
  rw [same] at r₂
  refine ⟨_, Nat.add_le_add_right hk _, _, r₁.trans r₂, ?_⟩
  simpa only [rows, TeamBurstEntry.rejection_code, StackOp.rename] using hr (.entry TeamBurstEntry.rejection)

/-- On invalid operands the callback deterministically reaches a rejecting halt. -/
theorem start_invalid (target : StackCode K R) (ports : Port r → K) (hp : Function.Injective ports)
    (label : State addr len → R) (resume : R)
    (hr : ∀ z, target (label z) = rows addr len ports label resume z) (base : Stacks K)
    (ready : Ready hw H addr len a q tick cap rs s) (bad : ¬ (q.val ≤ cap.val ∧ a.val+q.val ≤ 2^w)) :
    ∃ n ≤ rejectCost w, ∃ state bank, StackRuns target n (label (start addr len)) (installStacks ports base s)
      state bank ∧ target state = .halt false := by
  obtain ⟨t,ht,b,run,halt⟩ := start_invalid_label target ports hp label resume hr base ready bad
  exact ⟨t,ht,_,b,run,halt⟩

end TeamBurstCallback

end BorderVNP
end Computability
end OAI
