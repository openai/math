import OAI.Computability.NearSquareRoot.ScheduleChunkControl
import OAI.Computability.NearSquareRoot.ScheduleChunkPhases

/-!
# Peak heights in the physical chunk controller

The digit call starts with the caller's record parked on register zero and
the arguments on register one. The controller and all of its intermediate
compiler states have a common linear height bound. The digit call contributes
its own peak height once, even over a quadratic number of invocations.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkControl

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open ChunkLoop ChunkTask ChunkDispatch ChunkPhases
open Schoolbook (raw Segment)

noncomputable def digitBlock (d : Driver) (c : Cmd) (m : Operands → Word) (p : Input)
    (t bound H : ℕ) : Prop :=
  let cmd := program d c
  Block cmd (beginPhase cmd .digit (frame (p.bundle m t) (send (digitQuery m p t))))
    (endPhase cmd .digit (frame (p.bundle m t) (send (digitReply m p t)))) bound H

/-- All internal controller operations are charged to a segment with linear
cost, while its scratch space is reused at each digit pair. -/
theorem run (d : Driver) (c : Cmd) (m : Operands → Word) (p : Input) (C T S : ℕ)
    {result : List Ltr} (ctl : Calls d.load d.test d.prepare d.collect d.emit C m p result)
    (width : ∀ t < p.count, (digitReply m p t).length = 2*p.u)
    (call : ∀ t < p.count, digitBlock d c m p t T (max ((C+34)*(p.n+1)) S)) :
    let cmd := program d c
    Block cmd (beginPhase cmd .load (raw (input p)))
      (endPhase cmd .emit (raw result))
      ((p.count+1)*(3*(C*(p.n+1))+T+5)) (max ((C+34)*(p.n+1)) S) := by
  let cmd := program d c
  let R := 32*(p.n+1)
  let B := C*(p.n+1)
  let H := max ((C+34)*(p.n+1)) S
  have hcap : (C+34)*(p.n+1) ≤ H := Nat.le_max_left ..
  have hwork : R+B ≤ H := by dsimp [R,B]; rw [Nat.add_mul] at hcap; omega
  have hdispatch : R+2 ≤ H := by dsimp [R]; rw [Nat.add_mul] at hcap; omega
  let cfg (t : ℕ) := beginPhase cmd .test (raw (record m p t))
  have hrec (t : ℕ) (ht : t ≤ p.count) : (record m p t).length ≤ R := by
    have h := ChunkPhases.record_length m p t ht
    dsimp [R]; omega
  have hreg (t : ℕ) (ht : t ≤ p.count) : Height (raw (record m p t)) R :=
    ChunkControl.raw_height _ (hrec _ ht)
  have hinput : Height (raw (input p)) R := ChunkControl.raw_height _ (input_length p)
  have first : Block cmd (beginPhase cmd .load (raw (input p))) (cfg 0) (B+1) H :=
    (block_run (cmd:=cmd) (f:=.load) ctl.load_run hinput hwork).trans
      (block_skip (f:=.load) (g:=.test) rfl (hreg 0 (Nat.zero_le _)) (by omega))
  have step (t : ℕ) (ht : t < p.count) :
      Block cmd (cfg t) (cfg (t+1)) (3*B+T+4) H := by
    have testRun := ctl.test_run t ht.le
    rw [decide_eq_false (Nat.ne_of_lt ht)] at testRun
    have a := block_run (cmd:=cmd) (f:=.test) testRun (hreg _ ht.le) hwork
    have b := block_test (cmd:=cmd) (record m p t) false
      (show (record m p t).length+2 ≤ H from (Nat.add_le_add_right (hrec _ ht.le) 2).trans hdispatch)
    have c₁ := block_run (cmd:=cmd) (f:=.prepare) (ctl.prepare_run _ ht) (hreg _ ht.le) hwork
    have c₂ := block_skip (cmd:=cmd) (f:=.prepare) (g:=.digit) rfl
      (query_frame_height m p t ht.le) (by omega : R+1 ≤ H)
    have d₁ := call t ht
    have d₂ := block_skip (cmd:=cmd) (f:=.digit) (g:=.collect) rfl
      (reply_frame_height m p t ht.le (width t ht)) (by omega : R+1 ≤ H)
    have e₁ := block_run (cmd:=cmd) (f:=.collect) (ctl.collect_run _ ht (width _ ht))
      (reply_frame_height m p t ht.le (width t ht)) hwork
    have e₂ := block_skip (cmd:=cmd) (f:=.collect) (g:=.test) rfl
      (hreg _ ht) (by omega : R+1 ≤ H)
    exact (((((((a.trans b).trans c₁).trans c₂).trans d₁).trans d₂).trans e₁).trans e₂).enlarge
      (by omega)
  obtain ⟨w,hw,middle⟩ := Schoolbook.segments_iterate (m := machine cmd) p.count
    (fun j => (begin_height cmd .test _ R (hreg 0 (Nat.zero_le _)) j).trans (by omega)) step
  have last : Block cmd (cfg p.count) (endPhase cmd .emit (raw result)) (B+1+B) H := by
    have testRun := ctl.test_run p.count le_rfl
    rw [decide_eq_true rfl] at testRun
    have a := block_run (cmd:=cmd) (f:=.test) testRun (hreg _ le_rfl) hwork
    have b := block_test (cmd:=cmd) (record m p p.count) true
      (show (record m p p.count).length+2 ≤ H from (Nat.add_le_add_right (hrec _ le_rfl) 2).trans hdispatch)
    exact (a.trans b).trans (block_run (cmd:=cmd) (f:=.emit) ctl.emit_run (hreg _ le_rfl) hwork)
  have mid : Block cmd (cfg 0) (cfg p.count) (p.count*(3*B+T+4)) H := ⟨w,hw,middle⟩
  refine ((first.trans mid).trans last).enlarge ?_
  change B+1 + p.count*(3*B+T+4) + (B+1+B) ≤ (p.count+1)*(3*B+T+5)
  rw [Nat.add_mul]
  have := Nat.mul_le_mul_left p.count (show 3*B+T+4 ≤ 3*B+T+5 by omega)
  omega

end ChunkControl

end NearSquareRoot
end Computability
end OAI
