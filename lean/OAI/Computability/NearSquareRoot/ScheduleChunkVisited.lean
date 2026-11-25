import OAI.Computability.NearSquareRoot.ScheduleChunkGuard
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSpace
import OAI.Computability.NearSquareRoot.ScheduleSchoolIO

/-!
# Recovering callee stack bounds from physical space

The stack compiler keeps the absolute address just beyond the bottom of each
stack fixed. A bound on the cells visited by its released multitape machine
therefore bounds the stack heights at every source prefix, including inside
the callee.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkVisited

open IntegerMultiplication

/-- A physical space certificate for the released machine covers all stack
heights during the supplied run. The allowed clock can include the output
drain or any later bookkeeping. -/
theorem segment_of_released_visits {A Q I : Type} [DecidableEq I] {g : SM.Rule A Q I}
    {q : Q} {i k : I} {s : List A} {x : SM.Config A Q I} {n budget S : ℕ}
    (run : Trace (SM.advance g) (SM.origin q i s) n x)
    (clock : 2*n ≤ budget)
    (visited : VisitsAtMost (SM.complete k g) (ChunkGuard.origin q i s) budget S) :
    Schoolbook.Segment g (SM.origin q i s) n x (s.length + S) := by
  refine ⟨run, ?_⟩
  intro u z hu trace j
  let blank : TM.Tape (Option A) := TM.Tape.loaded none []
  let T (j : I) := if j = i then TM.Tape.loaded none (s.map some) else blank
  have repr : SM.faithful (SM.origin q i s).stack T := by
    intro l
    by_cases eq : l = i
    · subst l
      simpa [SM.origin, T] using SM.display_loaded s
    · simpa [SM.origin, T, eq, blank] using SM.display_loaded ([] : List A)
  obtain ⟨T', _, bottom, executed⟩ := simulateWithBottom trace T repr
  have lifted := SM.lift_many (k := k) executed blank
  have init :
      SM.configOut (TM.Config.mk (Sum.inl q : SM.PC A Q I) T) blank =
        ChunkGuard.origin q i s := by
    unfold SM.configOut ChunkGuard.origin
    congr 1
    funext l
    cases l <;> simp [T, blank]
  change Trace (TM.advance (SM.complete k g))
    (SM.configOut (TM.Config.mk (Sum.inl q : SM.PC A Q I) T) blank) (2*u) _ at lifted
  rw [init] at lifted
  have disp := Uniform.radius_of_visits visited (by omega) lifted (some j)
  change ((ChunkGuard.origin q i s).tape (some j)).pos - (S : ℤ) ≤ (T' j).pos ∧ _ at disp
  have h₀ : ((ChunkGuard.origin q i s).tape (some j)).pos = 0 := by
    by_cases hj : j = i <;> simp [ChunkGuard.origin, hj, TM.Tape.loaded]
  have hb : (T j).pos = 0 := by
    by_cases hj : j = i <;> simp [T, blank, hj, TM.Tape.loaded]
  have hs : ((SM.origin q i s).stack j).length ≤ s.length := by
    by_cases hj : j = i <;> simp [SM.origin, hj]
  have ht := bottom j
  rw [hb, zero_add] at ht
  rw [h₀] at disp
  omega

open IntegerMultiplication.Code
open Classical

/-- Register zero in the canonical stack compilation. -/
def inputReg (U : List (Prog.Loc Ltr)) : Prog.Ix U := some ⟨0, by simp [Prog.used]⟩

/-- The top-level entry point of a complete finite program table. -/
def start (U : List (Prog.Loc Ltr)) (c : Cmd) (good : Prog.Good U [] c) : Prog.Pc U :=
  some ⟨([],c), good (Prog.sites_self _ _)⟩

theorem canonical_origin (U : List (Prog.Loc Ltr)) (q : Prog.Pc U) (s : List Ltr) :
    Prog.machine U q (Schoolbook.raw s) [] = SM.origin q (inputReg U) (s.map Sum.inl) := by
  classical
  change SM.Config.mk _ _ = SM.Config.mk _ _
  rw [SM.Config.mk.injEq]
  refine ⟨rfl, funext fun i => ?_⟩
  cases i with
  | none => rfl
  | some j =>
    change ((Schoolbook.raw s) j.val).map Sum.inl =
      if some j = inputReg U then _ else []
    by_cases hj : j.val = 0
    · have e : some j = inputReg U := congrArg some (Subtype.ext hj)
      simp [Schoolbook.raw, hj, e]
    · have e : some j ≠ inputReg U := fun he => hj (congrArg Subtype.val (Option.some.inj he))
      simp [Schoolbook.raw, hj, e]

/-- Specialization to a program with all input letters on register zero.
This supplies the canonical segment required to relocate the callee's
registers while retaining the surrounding frame. -/
theorem compiled_segment (U : List (Prog.Loc Ltr)) {c : Cmd} (good : Prog.Good U [] c)
    {r : Reg Ltr} {s : List Ltr} {t budget S : ℕ}
    (source : Prog.Run [] c (Schoolbook.raw s) t r) (clock : 2*t ≤ budget)
    (visits : VisitsAtMost (SM.complete (inputReg U) (Prog.compile U))
      (ChunkGuard.origin (start U c good) (inputReg U) (s.map Sum.inl)) budget S) :
    Schoolbook.Segment (Prog.compile U) (Prog.machine U (start U c good) (Schoolbook.raw s) []) t
      (Prog.machine U none r []) (s.length + S) := by
  classical
  have run : Trace (SM.advance (Prog.compile U))
      (Prog.machine U (start U c good) (Schoolbook.raw s) []) t (Prog.machine U none r []) := by
    have h := source.compile_ok U good (fun i => by simp) []
    convert h using 2
    change some _ = if h : ([], c) ∈ U then some _ else none
    rw [dite_eq_left (good (Prog.sites_self _ _))]
  rw [canonical_origin] at run ⊢
  simpa only [List.length_map] using segment_of_released_visits run clock visits

end ChunkVisited

end NearSquareRoot
end Computability
end OAI
