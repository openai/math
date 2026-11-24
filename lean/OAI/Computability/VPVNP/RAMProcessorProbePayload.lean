import OAI.Computability.VPVNP.RAMProcessorProbeFields
import OAI.Computability.VPVNP.SliceArithmeticCallClear

/-!
# Probe record payloads and call returns

External writes copy both source registers to the record fields. External
reads stage the address before assigning the guessed word to its destination,
so a read may use the same register for its address and destination. A call
return copies the next persistent state and signals that the RAM is running.
An accepting call signals that execution has finished.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ProbeStages

open BurstRAM

variable {r k w : ℕ}

/-- Tag three marks an external write record. -/
def writePayload (addr src : Fin r) : FiniteRoutine (Port r k) :=
  ((setTag 3).followedBy (copy (.address addr))).followedBy (copy (.value src))

/-- The write fields contain the register values at the start of the probe. -/
theorem writePayload_run (addr src : Fin r) (s : Bank r k) (p a v : Word w)
    (hp : s.isa .persistent = wordBits p) (ha : s.isa (.reg addr) = wordBits a)
    (hv : s.isa (.reg src) = wordBits v) :
    (writePayload addr src).Runs (s.tag.length + s.address.length + s.value.length + 21*w + 9)
      s.stacks ({s with
        tag := wordBits (Fin.ofNat (2^w) 3), address := wordBits a, value := wordBits v} : Bank r k).stacks := by
  let tagged : Bank r k := {s with tag := wordBits (Fin.ofNat (2^w) 3)}
  let addressed : Bank r k := {tagged with address := wordBits a}
  have tag := tag_run 3 s p hp
  have address := copy_run (.address addr) tagged
  have value := copy_run (.value src) addressed
  simp only [tagged, addressed, Transfer.src, Transfer.dst, Transfer.set, Bank.stacks, ha, hv,
    length_wordBits] at address value
  unfold writePayload
  convert (tag.followedBy address).followedBy value using 1
  omega

/-- Tag two marks an external read. Copy the old address before assigning
the guessed word from the value field. -/
def readPayload (dst addr : Fin r) : FiniteRoutine (Port r k) :=
  ((setTag 2).followedBy (copy (.address addr))).followedBy (copy (.assign dst))

/-- The read record retains the address, even when the guessed value replaces
that address in the architectural bank. -/
theorem readPayload_run (dst addr : Fin r) (s : Bank r k) (p a v : Word w)
    (hp : s.isa .persistent = wordBits p) (ha : s.isa (.reg addr) = wordBits a)
    (hv : s.value = wordBits v) :
    (readPayload dst addr).Runs
      (s.tag.length + s.address.length + (s.isa (.reg dst)).length + 21*w + 9) s.stacks
      ({s with tag := wordBits (Fin.ofNat (2^w) 2), address := wordBits a,
               isa := Function.update s.isa (.reg dst) (wordBits v)} : Bank r k).stacks := by
  let tagged : Bank r k := {s with tag := wordBits (Fin.ofNat (2^w) 2)}
  let addressed : Bank r k := {tagged with address := wordBits a}
  have tag := tag_run 2 s p hp
  have address := copy_run (.address addr) tagged
  have assign := copy_run (.assign dst) addressed
  simp only [tagged, Transfer.src, Transfer.dst, Transfer.set, Bank.stacks, ha, length_wordBits] at address
  simp only [tagged, addressed, Transfer.src, Transfer.dst, Transfer.set, Bank.stacks] at assign
  have run := (tag.followedBy address).followedBy assign
  unfold readPayload
  simp only [hv, length_wordBits] at run ⊢
  convert run using 1
  omega

private def status (b : Bool) : FiniteRoutine (Port r k) :=
  (SliceArithmetic.CallClear.clear (.inr .running)).followedBy (.ofRoutine (Routine.push (.inr .running) b))

private theorem status_run (b : Bool) (s : Bank r k) :
    (status b).Runs (s.running.length + 2) s.stacks ({s with running := [b]} : Bank r k).stacks := by
  let p : Port r k := .inr .running
  let empty := Function.update s.stacks p []
  have clear := SliceArithmetic.CallClear.clear_runs p s.stacks
  have push : (FiniteRoutine.ofRoutine (Routine.push p b)).Runs 1 empty
      (Function.update empty p (b :: empty p)) := Routine.runs_push p b empty
  have he : Function.update empty p (b :: empty p) = ({s with running := [b]} : Bank r k).stacks := by
    funext i
    rcases i with i | i
    · rfl
    · cases i <;> rfl
  rw [he] at push
  exact clear.followedBy push

/-- Return a register as the persistent input for the next call. -/
def returnState (src : Fin r) : FiniteRoutine (Port r k) :=
  (copy (.returnState src)).followedBy (status true)

theorem returnState_run (src : Fin r) (s : Bank r k) (p v : Word w)
    (hp : s.isa .persistent = wordBits p) (hv : s.isa (.reg src) = wordBits v) :
    (returnState src).Runs (8*w + s.running.length + 5) s.stacks
      ({s with isa := Function.update s.isa .persistent (wordBits v), running := [true]} : Bank r k).stacks := by
  have state := copy_run (.returnState src) s
  simp only [Transfer.src, Transfer.dst, Transfer.set, Bank.stacks, hp, hv, length_wordBits] at state
  have finish := status_run true ({s with isa := Function.update s.isa .persistent (wordBits v)} : Bank r k)
  unfold returnState
  convert state.followedBy finish using 1
  dsimp only
  omega

/-- A final accepting call writes the stopped status. -/
def accept : FiniteRoutine (Port r k) := status false

theorem accept_run (s : Bank r k) :
    accept.Runs (s.running.length + 2) s.stacks ({s with running := [false]} : Bank r k).stacks :=
  status_run false s

end RAMTape.ProbeStages

end VPVNP
end Computability
end OAI
