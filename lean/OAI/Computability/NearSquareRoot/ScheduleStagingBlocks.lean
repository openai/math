import OAI.Computability.NearSquareRoot.ScheduleStagingOpen
import OAI.Computability.NearSquareRoot.ScheduleStagingPhases

/-!
# Controller runs between physical digit calls

The controller yields on the digit phase with the raw request in register one.
Once the callee has replaced it with a raw answer, the collect phase resumes
with the same parked record. The bounds below include the dispatch steps.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingBlocks

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open ChunkTask ChunkLoop ChunkDispatch
open ChunkPhases (input record digitQuery digitReply)
open Schoolbook (raw Segment)
open StagingPhases (Calls slot request)

abbrev Block (d : ChunkControl.Driver) (x y : Config (StagingOpen.cmd d))
    (budget height : ℕ) : Prop :=
  ∃ ticks ≤ budget, Segment (StagingOpen.rule d) x ticks y height

variable {C : ℕ} {m : Operands → Word} {p : Input} {result : List Ltr}

private theorem record_bound (m : Operands → Word) (p : Input) (t : ℕ) (ht : t ≤ p.count) :
    (record m p t).length ≤ 32*(p.n+1) := by
  have := ChunkPhases.record_length m p t ht
  omega

private theorem phase (d : ChunkControl.Driver) {f : ChunkControl.Phase} {r s : Reg Ltr}
    (hf : f ≠ .digit) (run : ChunkPhases.Runs (StagingOpen.cmd d f) (C*(p.n+1)) r s)
    (hr : ChunkControl.Height r (32*(p.n+1))) :
    Block d (beginPhase (StagingOpen.cmd d) f r) (endPhase (StagingOpen.cmd d) f s)
      (C*(p.n+1)) ((C+34)*(p.n+1)) := by
  obtain ⟨t,ht,run⟩ := run
  exact ⟨t,ht,StagingOpen.phase d hf run hr ht (by rw [Nat.add_mul]; omega)⟩

private theorem next (d : ChunkControl.Driver) {f g : ChunkControl.Phase} {s : Reg Ltr}
    (hf : f ≠ .digit)
    (branch : ChunkControl.route (StagingOpen.cmd d) f (SM.tops (endPhase (StagingOpen.cmd d) f s))
      = some (g,false))
    (hr : ChunkControl.Height s (32*(p.n+1))) :
    Segment (StagingOpen.rule d) (endPhase (StagingOpen.cmd d) f s) 1
      (beginPhase (StagingOpen.cmd d) g s) ((C+34)*(p.n+1)) :=
  StagingOpen.skip d hf branch hr (by rw [Nat.add_mul]; omega)

variable (d : ChunkControl.Driver) (ctl : Calls d.load d.test d.prepare d.collect d.emit C m p result)
include ctl

/-- Load the encoded external input and enter the first cursor test. -/
theorem launch :
    Block d (beginPhase (StagingOpen.cmd d) .load (raw (input p)))
      (beginPhase (StagingOpen.cmd d) .test (raw (record m p 0))) (C*(p.n+1)+1)
      ((C+34)*(p.n+1)) := by
  obtain ⟨t,ht,run⟩ := phase d (f := .load) (by decide) ctl.load_run
    (ChunkControl.raw_height _ (ChunkPhases.input_length p))
  have handoff := next (C := C) d (f := .load) (g := .test) (by decide) rfl
    (ChunkControl.raw_height _ (record_bound m p 0 (Nat.zero_le _)))
  exact ⟨t+1,by omega,run.trans handoff⟩

/-- A nonterminal cursor test places the raw request in register one and
yields to the external digit routine. -/
theorem offer (t : ℕ) (ht : t < p.count) :
    Block d (beginPhase (StagingOpen.cmd d) .test (raw (record m p t)))
      (beginPhase (StagingOpen.cmd d) .digit (slot (p.bundle m t) (request (digitQuery m p t))))
      (2*(C*(p.n+1))+2) ((C+34)*(p.n+1)) := by
  have testRun := ctl.test_run t ht.le
  rw [decide_eq_false ht.ne] at testRun
  have size := record_bound m p t ht.le
  have height := ChunkControl.raw_height _ size
  obtain ⟨x,hx,test⟩ := phase d (f := .test) (by decide) testRun height
  have branch := StagingOpen.test d (record m p t) false
    (H := (C+34)*(p.n+1)) (by rw [Nat.add_mul]; omega)
  obtain ⟨y,hy,prep⟩ := phase d (f := .prepare) (by decide) (ctl.prepare_run t ht) height
  have handoff := next (C := C) d (f := .prepare) (g := .digit) (by decide) rfl
    (StagingPhases.request_height m p t ht.le)
  exact ⟨_,by omega,((test.trans branch).trans prep).trans handoff⟩

/-- Parse the returned raw bits, add the digit product, and enter the next
cursor test. -/
theorem recover (t : ℕ) (ht : t < p.count) (width : (digitReply m p t).length = 2*p.u) :
    Block d (beginPhase (StagingOpen.cmd d) .collect
        (slot (p.bundle m t) ((digitReply m p t).map Ltr.bit)))
      (beginPhase (StagingOpen.cmd d) .test (raw (record m p (t+1)))) (C*(p.n+1)+1)
      ((C+34)*(p.n+1)) := by
  obtain ⟨x,hx,run⟩ := phase d (f := .collect) (by decide) (ctl.collect_run t ht width)
    (StagingPhases.result_height m p t ht.le width)
  have handoff := next (C := C) d (f := .collect) (g := .test) (by decide) rfl
    (ChunkControl.raw_height _ (record_bound m p (t+1) ht))
  exact ⟨x+1,by omega,run.trans handoff⟩

/-- The exhausted cursor dispatches to the final output command and reaches
its halt configuration. -/
theorem complete :
    Block d (beginPhase (StagingOpen.cmd d) .test (raw (record m p p.count)))
      (endPhase (StagingOpen.cmd d) .emit (raw result)) (2*(C*(p.n+1))+1)
      ((C+34)*(p.n+1)) := by
  have testRun := ctl.test_run p.count le_rfl
  rw [decide_eq_true rfl] at testRun
  have size := record_bound m p p.count le_rfl
  have height := ChunkControl.raw_height _ size
  obtain ⟨x,hx,test⟩ := phase d (f := .test) (by decide) testRun height
  have branch := StagingOpen.test d (record m p p.count) true
    (H := (C+34)*(p.n+1)) (by rw [Nat.add_mul]; omega)
  obtain ⟨y,hy,emit⟩ := phase d (f := .emit) (by decide) ctl.emit_run height
  exact ⟨_,by omega,(test.trans branch).trans emit⟩

end StagingBlocks

end NearSquareRoot
end Computability
end OAI
