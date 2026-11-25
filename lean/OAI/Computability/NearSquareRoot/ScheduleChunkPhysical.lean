import OAI.Computability.NearSquareRoot.ScheduleChunkMachine
import OAI.Computability.NearSquareRoot.ScheduleChunkGuard
import OAI.Computability.NearSquareRoot.ScheduleChunkProduct

/-!
# The guarded chunk controller on finite tapes

A common radius bounds every work head, including the fresh output tape.
On a valid shape each short multiplication need only fit this radius on the
current digit width. The same rule confines all cutoffs of unsuccessful trials.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkControl

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open ChunkLoop ChunkTask ChunkDispatch ChunkPhases

/-- This radius covers the scratch registers, return stack, and output copy. -/
def radius (C n : ℕ) := 2*((C+34)*(n+1))+2

noncomputable abbrev guarded (d : Driver) (c : Cmd) :=
  let cmd := program d c
  ChunkGuard.rule (ChunkDispatch.output cmd) (machine cmd)

noncomputable def initial (d : Driver) (c : Cmd) (R : ℕ) (s : List Ltr) :=
  let cmd := program d c
  ChunkGuard.initial (A := Prog.Sym (area cmd)) R (start cmd .load) (ChunkDispatch.output cmd) (s.map Sum.inl)

noncomputable abbrev tapeCount (d : Driver) (c : Cmd) :=
  Fintype.card (Option (Prog.Ix (area (program d c))))

/-- Every prefix of any trial uses this box, including trials with invalid
inputs and candidates that do not terminate. -/
theorem guarded_space (d : Driver) (c : Cmd) (C n budget : ℕ) (s : List Ltr) :
    VisitsAtMost (guarded d c) (initial d c (radius C n) s) budget
      (tapeCount d c * (2*radius C n+1)) :=
  ChunkGuard.visited _ _ _ _ _ _ _

/-- Run the controller through its final physical halt and output copy.
The polynomial bound applies to actual tape transitions. -/
theorem guarded_run_letters (d : Driver) (c : Cmd) (m : Operands → Word) (p : Input) (C T : ℕ)
    {result : List Ltr} (ctl : Calls d.load d.test d.prepare d.collect d.emit C m p result)
    (width : ∀ t < p.count, (digitReply m p t).length = 2*p.u)
    (hlen : result.length ≤ 4*p.n+1)
    (call : ∀ t < p.count, digitBlock d c m p t T ((C+34)*(p.n+1))) :
    ∃ t ≤ (6*C+16)*((p.count+1)*(p.n+T+1)), ∃ z,
      Trace (TM.advance (guarded d c)) (initial d c (radius C p.n) (input p)) t z ∧
      TM.advance (guarded d c) z = none ∧ z.pc.1 = false ∧
      TM.whole none ((result.map Sum.inl).map some) (ChunkGuard.data (z.tape none)) := by
  let cmd := program d c
  let H := (C+34)*(p.n+1)
  have h := run d c m p C T 0 ctl width (by simpa using call)
  obtain ⟨s,hs,cpu⟩ := h
  have hh : Schoolbook.Segment (machine cmd)
      (SM.origin (start cmd .load) (ChunkDispatch.output cmd) ((input p).map Sum.inl)) s
      (endPhase cmd .emit (Schoolbook.raw result)) H := by
    rw [← begin_origin]
    simpa only [Nat.max_zero] using cpu
  obtain ⟨z, done, halt, flag, out⟩ := ChunkGuard.success (k := ChunkDispatch.output cmd)
    hh (halt_output _) (R := radius C p.n) (le_refl _)
  have hout : ((endPhase cmd .emit (Schoolbook.raw result)).stack
      (ChunkDispatch.output cmd)) = result.map Sum.inl := rfl
  rw [hout] at done out
  refine ⟨_, ?_, z, done, halt, flag, out⟩
  simp only [List.length_map]
  have hbase : 3*(C*(p.n+1)) + T+5 ≤ (3*C+5)*(p.n+T+1) := by
    have h := Nat.mul_le_mul_left (3*C) (show p.n+1 ≤ p.n+T+1 by omega)
    calc
      _ = (3*C)*(p.n+1)+T+5 := by ring
      _ ≤ (3*C)*(p.n+T+1)+T+5 := by omega
      _ ≤ _ := by rw [Nat.add_mul]; omega
  have hmul := Nat.mul_le_mul_left (p.count+1) hbase
  rw [show (p.count+1)*((3*C+5)*(p.n+T+1)) = (3*C+5)*((p.count+1)*(p.n+T+1)) by ring] at hmul
  have hp : p.n+T+1 ≤ (p.count+1)*(p.n+T+1) :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have he : (6*C+16)*((p.count+1)*(p.n+T+1)) =
      2*((3*C+5)*((p.count+1)*(p.n+T+1))) + 6*((p.count+1)*(p.n+T+1)) := by ring
  rw [he]
  omega

/-- Run the controller through its final physical halt and output copy.
The polynomial bound applies to actual tape transitions. -/
theorem guarded_run (d : Driver) (c : Cmd) (m : Operands → Word) (p : Input) (C T : ℕ)
    (ctl : Calls d.load d.test d.prepare d.collect d.emit C m p)
    (width : ∀ t < p.count, (digitReply m p t).length = 2*p.u)
    (correct : ∀ q : EqualWords, bitValue (m q.val) = bitValue q.val.1 * bitValue q.val.2)
    (call : ∀ t < p.count, digitBlock d c m p t T ((C+34)*(p.n+1))) :
    ∃ t ≤ (6*C+16)*((p.count+1)*(p.n+T+1)), ∃ z,
      Trace (TM.advance (guarded d c)) (initial d c (radius C p.n) (input p)) t z ∧
      TM.advance (guarded d c) z = none ∧ z.pc.1 = false ∧
      TM.whole none (((send (answer m p)).spell.map Sum.inl).map some) (ChunkGuard.data (z.tape none)) ∧
      (answer m p).length = 2*p.n ∧ bitValue (answer m p) = bitValue p.x * bitValue p.y := by
  have hz := answer_spec m correct p
  have hlen : (ChunkPhases.output m p).length ≤ 4*p.n+1 := by
    change (send (answer m p)).spell.length ≤ _
    rw [Tree.spell_length]
    change size (answer m p) ≤ _
    rw [size_word, hz.1]
    omega
  obtain ⟨t, ht, z, run, halt, flag, out⟩ := guarded_run_letters d c m p C T ctl width hlen call
  exact ⟨t, ht, z, run, halt, flag, out, hz⟩

end ChunkControl

end NearSquareRoot
end Computability
end OAI
