import OAI.Computability.NearSquareRoot.ScheduleStagingOpen
import OAI.Computability.NearSquareRoot.ScheduleStagingPhases
import OAI.Computability.NearSquareRoot.ShortWordSpace

/-!
# Physical controller with fixed stack-bottom coordinates

A faithful stack at a given bottom determines the entire physical tape.
Consequently every bounded controller segment has a unique physical start
and finish on the same bottom coordinates, even across a parked digit call.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingControl

open IntegerMultiplication

variable {A Q I : Type}

def tape (bottom : ℤ) (s : List A) : TM.Tape (Option A) :=
  ⟨bottom-(s.length : ℤ),SM.display s⟩

def tapes (bottom : I → ℤ) (s : I → List A) : I → TM.Tape (Option A) :=
  fun j => tape (bottom j) (s j)

def physical (bottom : I → ℤ) (x : SM.Config A Q I) : TM.Config (Option A) (SM.PC A Q I) I :=
  ⟨.inl x.pc,tapes bottom x.stack⟩

theorem faithful (bottom : I → ℤ) (s : I → List A) : SM.faithful s (tapes bottom s) := fun _ => rfl

theorem tapes_eq {s : I → List A} {T : I → TM.Tape (Option A)} {bottom : I → ℤ}
    (rep : SM.faithful s T) (h : ∀ j, (T j).pos+((s j).length : ℤ) = bottom j) : T = tapes bottom s := by
  funext j
  change (T j) = TM.Tape.mk _ _
  rw [TM.Tape.mk.injEq]
  exact ⟨by have := h j; omega, rep j⟩

/-- Each abstract step takes two physical transitions. The additive cell on
either side of the stack accommodates the compiler's intermediate state. -/
theorem segment {m : SM.Rule A Q I} {x y : SM.Config A Q I} {t H : ℕ}
    (run : Schoolbook.Segment m x t y H) (bottom : I → ℤ) :
    FencedRun (SM.toTM m) (fun i => bottom i-H-1) (fun i => bottom i+1)
      (physical bottom x) (2*t) (physical bottom y) := by
  obtain ⟨T,last,fixBottom,exec⟩ := simulateWithBottom run.run (tapes bottom x.stack) (faithful _ _)
  have eqT := tapes_eq last (bottom := bottom) (fun j => by
    rw [fixBottom]; change bottom j-((x.stack j).length : ℤ)+_ = _; omega)
  subst T
  refine ⟨exec,fun k hk z hz j => ?_⟩
  have f := stack_fence run.run (tapes bottom x.stack) (faithful _ _) j H
    (fun h tr => run.height h tr j) hk hz
  simpa only [tapes,tape,Int.sub_add_cancel] using f

/-- Start from any faithful tape family, including a family left by a call
that saved its own absolute bottoms. The resulting tapes are canonical. -/
theorem segment_from {m : SM.Rule A Q I} {x y : SM.Config A Q I} {t H : ℕ}
    (run : Schoolbook.Segment m x t y H) (T : I → TM.Tape (Option A)) (rep : SM.faithful x.stack T) :
    let B (j : I) := (T j).pos+((x.stack j).length : ℤ)
    FencedRun (SM.toTM m) (fun i => B i-H-1) (fun i => B i+1)
      ⟨.inl x.pc,T⟩ (2*t) (physical B y) := by
  dsimp only
  have result := segment run (fun j => (T j).pos+((x.stack j).length : ℤ))
  change FencedRun _ _ _ ⟨_,tapes _ _⟩ _ _ at result
  rwa [← tapes_eq rep (fun _ => rfl)] at result

theorem halt {m : SM.Rule A Q I} {x : SM.Config A Q I} (h : SM.advance m x = none) (B : I → ℤ) :
    TM.advance (SM.toTM m) (physical B x) = none :=
  SM.simulate_halt h (faithful _ _)

section Driver

open IntegerMultiplication.Code ChunkDispatch
open ChunkControl (Driver Phase)

variable (d : Driver)
local notation "cmd" => StagingOpen.cmd d

abbrev Axis := Prog.Ix (area cmd)
abbrev Letter := Option (Prog.Sym (area cmd))
abbrev State := SM.PC (Prog.Sym (area cmd)) (ChunkDispatch.Control cmd) (Axis d)

noncomputable abbrev rule := SM.toTM (StagingOpen.rule d)

def digit : State d → Bool
  | .inl (.digit,_) => true
  | _ => false

noncomputable def entry (B : Axis d → ℤ) (f : Phase) (r : Reg Ltr) :=
  physical B (beginPhase cmd f r)

noncomputable def returned (B : Axis d → ℤ) (f : Phase) (r : Reg Ltr) :=
  physical B (endPhase cmd f r)

/-- Pause at a digit request on arbitrary physical tapes, before inspecting
or changing any of their cells. -/
theorem pause (pc : Prog.Pc (area cmd)) (T : Axis d → TM.Tape (Letter d)) :
    TM.advance (rule d) ⟨.inl (.digit,pc),T⟩ = none := rfl

theorem finished (B : Axis d → ℤ) (r : Reg Ltr) :
    TM.advance (rule d) (returned d B .emit r) = none :=
  halt (StagingOpen.halt d r) B

@[simp] theorem digit_entry (B : Axis d → ℤ) (r : Reg Ltr) :
    digit d (entry d B .digit r).pc = true := rfl

@[simp] theorem digit_finished (B : Axis d → ℤ) (r : Reg Ltr) :
    digit d (returned d B .emit r).pc = false := rfl

/-- Bounded stage blocks can be composed at their physical endpoints. -/
theorem block {x y : ChunkDispatch.Config cmd} {cost H : ℕ}
    (h : ∃ t ≤ cost, Schoolbook.Segment (StagingOpen.rule d) x t y H) (B : Axis d → ℤ) :
    ∃ u ≤ 2*cost, FencedRun (rule d) (fun i => B i-H-1) (fun i => B i+1)
      (physical B x) u (physical B y) := by
  obtain ⟨t,ht,run⟩ := h
  exact ⟨2*t,Nat.mul_le_mul_left 2 ht,segment run B⟩

/-- Physical layout of the shared request and reply buffer, whose top may
move because the two bit strings have different lengths. -/
theorem one_tape (B : Axis d → ℤ) (f : Phase) (b : ChunkPhases.Bundle) (s : List Ltr) :
    (entry d B f (StagingPhases.slot b s)).tape (StagingOpen.one d) =
      tape (B (StagingOpen.one d)) (s.map Sum.inl) := by
  change tape _ ((beginPhase cmd f _).stack (StagingOpen.one d)) = _
  rw [StagingOpen.begin_one]
  simp [StagingPhases.slot]

/-- Replacing register one supplies the exact input tapes for the collection
phase. Every parked register, including the return stack, stays unchanged. -/
theorem replace_reply (B : Axis d → ℤ) (b : ChunkPhases.Bundle) (query reply : List Ltr) :
    (entry d B .collect (StagingPhases.slot b reply)).tape =
      Function.update (entry d B .digit (StagingPhases.slot b query)).tape (StagingOpen.one d)
        (tape (B (StagingOpen.one d)) (reply.map Sum.inl)) := by
  funext j
  by_cases eq : j = StagingOpen.one d
  · subst j
    rw [Function.update_self,one_tape]
  · rw [Function.update_of_ne eq]
    cases j with
    | none => rfl
    | some k =>
      have hk : k.val ≠ 1 := fun h => eq (congrArg some (Subtype.ext h))
      change tape _ (((StagingPhases.slot b reply) k.val).map Sum.inl) =
        tape _ (((StagingPhases.slot b query) k.val).map Sum.inl)
      simp only [StagingPhases.slot,Function.update_of_ne hk]

/-- At launch only the input register has a nonzero bottom. -/
def initialBottom (s : List Ltr) (j : Axis d) : ℤ :=
  if j = ChunkDispatch.output cmd then s.length else 0

theorem tape_loaded (s : List A) : tape (s.length : ℤ) s = TM.Tape.loaded none (s.map some) := by
  change TM.Tape.mk _ _ = TM.Tape.mk _ _
  rw [TM.Tape.mk.injEq]
  exact ⟨by omega,(SM.display_loaded s).symm⟩

theorem entry_input (s : List Ltr) :
    (entry d (initialBottom d s) .load (Schoolbook.raw s)).tape = fun j =>
      if j = ChunkDispatch.output cmd then TM.Tape.loaded none ((s.map Sum.inl).map some)
      else TM.Tape.loaded none [] := by
  funext j
  change tape _ ((beginPhase cmd .load (Schoolbook.raw s)).stack j) = _
  rw [begin_origin]
  by_cases h : j = ChunkDispatch.output cmd
  · simp only [SM.origin,h,ite_true,initialBottom]
    simpa only [List.length_map] using tape_loaded (s.map (Sum.inl (β := Prog.Ptr (area cmd))))
  · simp only [SM.origin,h,ite_false,initialBottom]
    exact tape_loaded []

theorem one_bottom (s : List Ltr) : initialBottom d s (StagingOpen.one d) = 0 := by
  simp [initialBottom,StagingOpen.one_ne_output]

end Driver

end StagingControl

end NearSquareRoot
end Computability
end OAI
