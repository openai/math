import OAI.Computability.BorderVNP.TeamTapeInputEmitWord
import Mathlib.Tactic.FinCases

/-! # Building the two physical slots for a time-zero team input word -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInputEmit

open VPVNP BurstRAM RAMTape RAMSerialization
open BurstRAM (wordBits)

/-- Width-limited integer written as one tape word. -/
abbrev word (w a : ℕ) : Word w := Fin.ofNat (2^w) a

/-- Physical read or write half of the initialization of one input bit. -/
def half (w a : ℕ) (b phase : Bool) : WordRecord w :=
  ⟨if phase then .write else .read, word w a, word w (phase && b).toNat, 0,
    word w (2*a+phase.toNat)⟩

/-- The corresponding four-word probe, before expansion into two ordered slots. -/
def probe (w a : ℕ) (b : Bool) : TeamRecords.Record (Word w) :=
  ⟨a, 0, 0, word w b.toNat⟩

/-- Both serialized halves are the physical representation of the time-zero probe. -/
theorem halves_eq_wordPair (w a : ℕ) (b : Bool) (h : 2*a+1 < 2^w) :
    [half w a b false, half w a b true] = TeamTapeSorting.wordPair (probe w a b)
      (show TeamTapeSorting.ProbeFits (probe w a b) from ⟨h, Nat.two_pow_pos w⟩) := by
  simp only [TeamTapeSorting.wordPair, List.cons.injEq, and_true]
  constructor <;> apply WordRecord.record_injective <;>
    simp [WordRecord.ofRecord, WordRecord.record, half, word, probe, TeamRecords.inputRecord, TeamRecords.outputRecord,
      Nat.mod_eq_of_lt (show a < 2^w by omega),
      Nat.mod_eq_of_lt (show 2*a < 2^w by omega), Nat.mod_eq_of_lt h]

/-- The five field computations in their physical serialization order. -/
def fieldOp (phase b : Bool) : Fin 5 → Op :=
  ![.literal (if phase then 3 else 2), .copy, .literal (phase && b).toNat, .literal 0, .double phase]

private theorem field_value {w a : ℕ} (hw : 2 ≤ w) (ha : a < 2^w) (phase b : Bool) (j : Fin 5) :
    word w ((fieldOp phase b j).eval (word w a).val) =
      (recordFormat hw).words (some (half w a b phase)) j := by
  have small : 4 ≤ 2^w := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  fin_cases j <;> cases phase <;> apply Fin.ext <;>
    first | rfl | (change (_ % (2^w)) = _; simp [fieldOp, Op.eval, word, half,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show 2 < 2^w by omega),
      Nat.mod_eq_of_lt (show 3 < 2^w by omega), recordFormat] <;> rfl)

/-- Between emissions the cursor and unread bits remain in their own ports; staged words
are bounded in length, and the buffer contains precisely the indicated record prefix. -/
structure Ready {w : ℕ} (hw : 2 ≤ w) (H a : ℕ) (bs : List Bool)
    (rs : List (WordRecord w)) (s : Stacks Port) : Prop where
  bits : s .bits = bs
  cursor : s .cursor = BurstRAM.wordBits (word w a)
  buffer : RecordBuffer.Holds hw H rs (s ∘ Port.buffer)
  fields : ∀ j, (s (.buffer (.field j))).length ≤ w

variable {w H a : ℕ} {hw : 2 ≤ w} {bs : List Bool} {rs : List (WordRecord w)} {s : Stacks Port}

private theorem updateField (ready : Ready hw H a bs rs s) (j : Fin 5) (z : Word w) :
    Ready hw H a bs rs (Function.update s (.buffer (.field j)) (BurstRAM.wordBits z)) := by
  refine ⟨by simpa using ready.bits, by simpa using ready.cursor, ?_, ?_⟩
  · rcases ready.buffer with ⟨h1,h2,h3,h4,h5,h6⟩
    exact ⟨h1, by simpa using h2, by simpa using h3, by simpa using h4,
      by simpa using h5, by simpa using h6⟩
  · intro i
    by_cases hij : i = j
    · subst i; simp
    · simpa [hij] using ready.fields i

private def stage (phase b : Bool) : List (Fin 5) → FiniteRoutine Port
  | [] => .ret
  | j :: js => (load (.stage j) (fieldOp phase b j)).followedBy (stage phase b js)

private theorem stage_runs (ready : Ready hw H a bs rs s) (ha : a < 2^w) (phase b : Bool)
    (js : List (Fin 5)) :
    ∃ t out, t ≤ js.length*(8*w+3)+1 ∧ (stage phase b js).Runs t s out ∧
      Ready hw H a bs rs out ∧
      ∀ j, out (.buffer (.field j)) =
        if j ∈ js then BurstRAM.wordBits ((recordFormat hw).words (some (half w a b phase)) j)
        else s (.buffer (.field j)) := by
  induction js generalizing s with
  | nil => exact ⟨1,s,by simp,Routine.runs_ret s,ready,by simp⟩
  | cons j js ih =>
    let z := (recordFormat hw).words (some (half w a b phase)) j
    let mid := Function.update s (.buffer (.field j)) (BurstRAM.wordBits z)
    have run := load_runs (.stage j) (fieldOp phase b j) s (word w a) ready.cursor
      ready.buffer.scratch ready.buffer.output
    simp only [Move.dst, field_value hw ha] at run
    obtain ⟨t,out,ht,hr,hs,hf⟩ := ih (s := mid) (updateField ready j z)
    refine ⟨_, out, ?_, run.followedBy hr, hs, ?_⟩
    · rw [List.length_cons, Nat.succ_mul js.length (8*w+3)]; have := ready.fields j; omega
    · intro i
      rw [hf]
      by_cases hi : i ∈ js <;> by_cases hj : i = j <;> simp_all [mid,z]

/-- Stage a complete five-word slot, then append it to the physical reverse buffer. -/
def emitHalf (phase b : Bool) : FiniteRoutine Port :=
  (stage phase b (List.finRange 5)).followedBy (RecordBuffer.appendRecord.onPorts Port.buffer)

/-- Emission restores the address and consumes exactly one free slot. Field one keeps the
address available to the subsequent increment even after the final write. -/
theorem emitHalf_runs (ready : Ready hw H a bs rs s) (ha : a < 2^w)
    (free : rs.length < 4*H) (phase b : Bool) :
    ∃ t out, t ≤ 65*w+28 ∧ (emitHalf phase b).Runs t s out ∧
      Ready hw H a bs (rs ++ [half w a b phase]) out ∧
      out (.buffer (.field 1)) = BurstRAM.wordBits (word w a) := by
  obtain ⟨t,mid,ht,hr,hm,hfields⟩ := stage_runs ready ha phase b (List.finRange 5)
  let r := half w a b phase
  have hf (j : Fin 5) : mid (.buffer (.field j)) = BurstRAM.wordBits ((recordFormat hw).words (some r) j) :=
    by simpa only [List.mem_finRange, ite_true] using hfields j
  obtain ⟨em, holds⟩ := hm.buffer.emit free r hf
  let small := RecordBuffer.emitted (mid ∘ Port.buffer) (List.replicate (4*H-(rs.length+1)) true)
    (List.ofFn ((recordFormat hw).encode (some r)))
  let out := installStacks Port.buffer mid small
  have hu (k : RecordBuffer.Port) : out (.buffer k) = small k := installStacks_at (fun _ _ he => Port.buffer.inj he) ..
  have ho {k : Port} (hk : ∀ p, Port.buffer p ≠ k) : out k = mid k := installStacks_outside _ _ hk
  have he : (RecordBuffer.appendRecord.onPorts Port.buffer).Runs (25*w+12) mid out := by
    exact RecordBuffer.appendRecord.runs_onPorts_framed (fun _ _ he => Port.buffer.inj he) em (fun _ => rfl) hu
      (fun _ hk => ho hk)
  refine ⟨_,out,?_,hr.followedBy he,?_,?_⟩
  · rw [List.length_finRange] at ht; omega
  · refine ⟨(ho (by simp)).trans hm.bits, (ho (by simp)).trans hm.cursor, ?_, ?_⟩
    · have eq : out ∘ Port.buffer = small := funext hu
      rw [eq]
      exact holds
    · intro j
      rw [hu]
      simpa [small, RecordBuffer.emitted] using hm.fields j
  · rw [hu]
    simpa [small, RecordBuffer.emitted, r, recordFormat, half] using hf 1

end TeamTapeInputEmit

end BorderVNP
end Computability
end OAI
