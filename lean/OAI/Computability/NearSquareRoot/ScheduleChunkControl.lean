import OAI.Computability.NearSquareRoot.ScheduleChunkDispatch
import OAI.Computability.NearSquareRoot.ScheduleSchoolSegments

/-!
# The physical control flow of a bounded chunk attempt

The row test leaves a Boolean above the current record. The driver consumes
this letter and leaves the record in place. The digit command and the fixed
controller commands always return to an empty return stack.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkControl

open IntegerMultiplication IntegerMultiplication.Code Schoolbook
open ChunkDispatch

inductive Phase | load | test | prepare | digit | collect | emit
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.load, .test, .prepare, .digit, .collect, .emit}
  complete i := by cases i <;> decide

structure Driver where
  load : Cmd
  test : Cmd
  prepare : Cmd
  collect : Cmd
  emit : Cmd

def program (d : Driver) (callee : Cmd) : Phase → Cmd
  | .load => d.load
  | .test => d.test
  | .prepare => d.prepare
  | .digit => callee.rename Nat.succ
  | .collect => d.collect
  | .emit => d.emit

variable (cmd : Phase → Cmd)

def route : Route cmd
  | .load, _ => some (.test, false)
  | .test, seen => match seen (ChunkDispatch.output cmd) with
    | some (.inl (.bit b)) => some (if b then .emit else .prepare, true)
    | _ => none
  | .prepare, _ => some (.digit, false)
  | .digit, _ => some (.collect, false)
  | .collect, _ => some (.test, false)
  | .emit, _ => none

noncomputable abbrev machine := rule cmd (route cmd)

/-- Actual stack-machine steps, with a single cap applying to every prefix. -/
abbrev Block (x y : Config cmd) (budget capacity : ℕ) :=
  ∃ t ≤ budget, Segment (machine cmd) x t y capacity

variable {cmd}

theorem Block.trans {x y z : Config cmd} {b b' H : ℕ}
    (hx : Block cmd x y b H) (hy : Block cmd y z b' H) : Block cmd x z (b+b') H := by
  obtain ⟨t, ht, h⟩ := hx
  obtain ⟨s, hs, g⟩ := hy
  exact ⟨t+s, Nat.add_le_add ht hs, h.trans g⟩

theorem Block.enlarge {x y : Config cmd} {b b' H : ℕ}
    (hx : Block cmd x y b H) (h : b ≤ b') : Block cmd x y b' H := by
  obtain ⟨t,ht,run⟩ := hx
  exact ⟨t,ht.trans h,run⟩

abbrev Height (s : Reg Ltr) (H : ℕ) := ∀ i, (s i).length ≤ H

theorem block_run {f : Phase} {r s : Reg Ltr} {R B H : ℕ}
    (h : ∃ t ≤ B, Prog.Run [] (cmd f) r t s) (hr : Height r R) (hh : R+B ≤ H) :
    Block cmd (beginPhase cmd f r) (endPhase cmd f s) B H := by
  obtain ⟨t,ht,run⟩ := h
  exact ⟨t, ht, (Segment.of_cost (run_phase cmd (route cmd) f run)
    (begin_height cmd f r R hr) ht).mono hh⟩

theorem block_skip {f g : Phase} {s : Reg Ltr} {R H : ℕ}
    (h : route cmd f (SM.tops (endPhase cmd f s)) = some (g,false))
    (hr : Height s R) (hh : R+1 ≤ H) :
    Block cmd (endPhase cmd f s) (beginPhase cmd g s) 1 H :=
  ⟨1, le_rfl, (Segment.of_cost (dispatch_skip cmd (route cmd) h) (end_height cmd f s R hr)
    le_rfl).mono hh⟩

theorem raw_height (s : List Ltr) {R : ℕ} (h : s.length ≤ R) : Height (raw s) R := by
  intro i
  by_cases hi : i = 0 <;> simp [raw,hi,h]

theorem block_test (s : List Ltr) (flag : Bool) {H : ℕ} (h : s.length+2 ≤ H) :
    Block cmd (endPhase cmd .test (raw (.bit flag::s)))
      (beginPhase cmd (if flag then .emit else .prepare) (raw s)) 1 H := by
  have tag : route cmd .test (SM.tops (endPhase cmd .test (raw (.bit flag :: s)))) =
      some (if flag then .emit else .prepare, true) := by
    rw [route,tops_output]
    rfl
  exact ⟨1,le_rfl,(Segment.of_cost (dispatch_pop_raw cmd (route cmd) (.bit flag) s tag)
    (end_height cmd .test _ (s.length+1) (raw_height _ le_rfl)) le_rfl).mono h⟩

theorem halt_output (r : Reg Ltr) : SM.advance (machine cmd) (endPhase cmd .emit r) = none :=
  halt_phase cmd (route cmd) rfl

end ChunkControl

end NearSquareRoot
end Computability
end OAI
