import OAI.Computability.BorderVNP.TeamBurstProbeControl
import OAI.Computability.BorderVNP.TeamBurstProbeEntry
import OAI.Computability.VPVNP.RAMTapeMapWord

/-! # Staging a private-call burst from architectural registers

The setup reads the chosen address and length registers without changing either one.
They may be the same register. It initializes the guesser's width template from the
timestamp, reuses the existing sorter buffer in place and passes the public cap directly
to the range guard. The previous burst cursor and other bounded scratch may be dirty.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamBurstCallbackSetup

open VPVNP BurstRAM RAMTape

variable {r w H : ℕ}

/-- Architectural sources, common emitter, entry guard and length decoder scratch. -/
inductive Port (r : ℕ)
  | reg (i : Fin r)
  | stamp | maxBurst
  | step (p : TeamBurstProbeStep.Port)
  | guard (p : TeamBurstGuard.Port)
  | high
  deriving DecidableEq, Fintype

private abbrev word (k : TeamProbeEmit.Operand) : Port r := .step (TeamBurstProbeStep.word k)

private abbrev tmp : Port r := .step (.probe .temp)

/-- The guard shares the probe address, the public cap, the countdown and private input. -/
def entryPorts : TeamBurstEntry.Port → Port r
  | .guard .address => word .address
  | .guard .cap => .maxBurst
  | .guard p => .guard p
  | .marks => .step .marks
  | .high => .high
  | .privateInput => .step .privateInput

/-- The entry submachine has distinct physical ports after mounting it in the callback. -/
theorem entryPorts_injective : Function.Injective (entryPorts (r := r)) := by
  intro i j h
  cases i <;> cases j <;> first
    | (rename_i p q; cases p <;> cases q <;> simp_all [entryPorts])
    | (rename_i p; cases p <;> simp_all [entryPorts])
    | simp_all [entryPorts]

/-- Exactly the reused stack locations erased before staging the burst. -/
def overwritten : List (Port r) :=
  [word .address, word .tick, word .before, word .after, tmp, .step .width, .step .saved,
   .step .marks, .step .privateReverse, .step .privateInput, .high, .guard .length,
   .guard .addressCopy, .guard .lengthCopy, .guard .capCopy, .guard .temp, .guard .flag]

/-- Physical precondition at a private-call opcode. Old word scratch may hold any word. -/
structure Ready (hw : 2 ≤ w+1) (H : ℕ) (addr len : Fin r) (a q tick cap : Word w)
    (rs : List (RAMSerialization.WordRecord (w+1))) (s : Stacks (Port r)) : Prop where
  /-- Current address register selected by the opcode. -/
  address : s (.reg addr) = wordBits a
  /-- Current length register selected by the opcode. -/
  length : s (.reg len) = wordBits q
  /-- First probe time supplied by the charging routine. -/
  time : s .stamp = wordBits tick
  /-- Public cap retained throughout the callback. -/
  capWord : s .maxBurst = wordBits cap
  /-- All discarded words and work stacks fit within the logical word width. -/
  short : ∀ i ∈ overwritten, (s i).length ≤ w
  /-- Widened emitter work registers from previous probes. -/
  lifted : ∀ i, (s (.step (.probe (.lifted i)))).length ≤ w+1
  /-- Already emitted physical slots in the sorter. -/
  buffer : RecordBuffer.Holds hw H rs (s ∘ Port.step ∘ TeamBurstProbeStep.Port.probe ∘ TeamProbeEmit.Port.buffer)
  /-- Reused physical record fields fit the sorter width. -/
  fields : ∀ j, (s (.step (.probe (.buffer (.field j))))).length ≤ w+1

/-- Precise post-setup bank, including the new guesses' width template. -/
def prepared (addr len : Fin r) (s : Stacks (Port r)) : Stacks (Port r)
  | .step (.probe (.operand .address)) => s (.reg addr)
  | .step (.probe (.operand .tick)) => s .stamp
  | .step (.probe (.operand _)) | .step (.probe .temp) => []
  | .step .width => List.replicate (s .stamp).length true
  | .step .saved | .step .marks | .step .privateReverse | .step .privateInput | .high => []
  | .guard .length => s (.reg len)
  | .guard .addressCopy | .guard .lengthCopy | .guard .capCopy | .guard .temp | .guard .flag => []
  | p => s p

/-- Fixed finite table for staging two source registers and the first timestamp. -/
def program (addr len : Fin r) : FiniteRoutine (Port r) :=
  ((((SliceArithmetic.CallClear.cleanup overwritten).followedBy
    (SuccessorFields.prependCopy (.reg addr) (word .address) tmp)).followedBy
    (SuccessorFields.prependCopy (.reg len) (.guard .length) tmp)).followedBy
    (SuccessorFields.prependCopy .stamp (word .tick) tmp)).followedBy
    (WordCopy.mapWord tmp (.step .width) (fun _ => true) .stamp)

variable {hw : 2 ≤ w+1} {a q tick cap : Word w}
variable {rs : List (RAMSerialization.WordRecord (w+1))} {s : Stacks (Port r)}

/-- The physical setup cost is independent of the requested length and the public cap. -/
theorem runs (addr len : Fin r) (h : Ready hw H addr len a q tick cap rs s) :
    ∃ n ≤ 60*(w+1), (program addr len).Runs n s (prepared addr len s) := by
  let clean := SliceArithmetic.CallClear.erased overwritten s
  obtain ⟨t,ht,clear⟩ := SliceArithmetic.CallClear.cleanup_runs overwritten s w h.short
  let copy (i j : Port r) (u : Stacks (Port r)) := Function.update u j (u i)
  let x := copy (.reg addr) (word .address) clean
  let y := copy (.reg len) (.guard .length) x
  let z := copy .stamp (word .tick) y
  have c1 := SuccessorFields.prependCopy_runs (.reg addr) (word .address) tmp (by simp)
    (by simp) (by simp) clean (by rfl)
  have c2 := SuccessorFields.prependCopy_runs (.reg len) (.guard .length) tmp (by simp)
    (by simp) (by simp) x (by rfl)
  have c3 := SuccessorFields.prependCopy_runs (.stamp : Port r) (word .tick) tmp (by simp)
    (by simp) (by simp) y (by rfl)
  have c4 := WordCopy.mapWord_run tmp (.step .width) (fun _ => true)
    (src := (Port.stamp : Port r)) (by simp) (by simp) (by simp) z (by rfl)
  have c1' : (SuccessorFields.prependCopy (.reg addr) (word .address) tmp).Runs (5*w+2) clean x := by
    simpa only [show clean (word .address) = [] from rfl, List.append_nil,
      show (clean (.reg addr)).length = w from (congrArg List.length h.address).trans (length_wordBits a)] using c1
  have c2' : (SuccessorFields.prependCopy (.reg len) (.guard .length) tmp).Runs (5*w+2) x y := by
    simpa only [show x (.guard .length) = [] from rfl, List.append_nil,
      show (x (.reg len)).length = w from (congrArg List.length h.length).trans (length_wordBits q)] using c2
  have c3' : (SuccessorFields.prependCopy .stamp (word .tick) tmp).Runs (5*w+2) y z := by
    simpa only [show y (word .tick) = [] from rfl, List.append_nil,
      show (y .stamp).length = w from (congrArg List.length h.time).trans (length_wordBits tick)] using c3
  have eq : Function.update z (.step .width) (List.replicate (z .stamp).length true) =
      prepared addr len s := by
    funext i
    cases i with
    | reg | stamp | maxBurst | high => rfl
    | guard k => cases k <;> rfl
    | step k =>
      cases k with
      | probe p =>
        cases p with
        | operand i => cases i <;> rfl
        | lifted | buffer | temp => rfl
      | _ => rfl
  rw [List.map_const', List.reverse_replicate, show z (.step .width) = [] from rfl,
    List.append_nil, eq, show (z .stamp).length = w from (congrArg List.length h.time).trans (length_wordBits tick)] at c4
  change t ≤ 17*(w+1)+1 at ht
  exact ⟨_, by omega, (((clear.followedBy c1').followedBy c2').followedBy c3').followedBy c4⟩

/-- The finite entry guard sees the same address as the burst probe and a clean countdown. -/
theorem entry_ready {addr len : Fin r} (h : Ready hw H addr len a q tick cap rs s) :
    TeamBurstEntry.Ready a q cap (prepared addr len s ∘ entryPorts) :=
  ⟨⟨h.address,h.length,h.capWord,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩

/-- Before the entry table installs the countdown, the loop is ready with zero markers. -/
theorem loop_ready {addr len : Fin r} (h : Ready hw H addr len a q tick cap rs s) :
    TeamBurstProbe.LoopReady hw H a tick rs [] 0 (prepared addr len s ∘ Port.step) :=
  ⟨⟨h.address,h.time,rfl,rfl,rfl,rfl,h.lifted,h.buffer,h.fields⟩,rfl,
    by change List.replicate (s .stamp).length true = _; rw [h.time, length_wordBits],rfl,rfl⟩

end TeamBurstCallbackSetup

end BorderVNP
end Computability
end OAI
