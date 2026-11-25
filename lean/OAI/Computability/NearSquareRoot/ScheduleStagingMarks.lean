import OAI.Computability.NearSquareRoot.ScheduleStagingProtection
import OAI.Computability.NearSquareRoot.ScheduleChunkGuardInit

/-! # Simultaneous installation of the two fence layers

The width tape is read-only. The marked work tapes comprise the staged bank
and its publication tape. Only the former receives an inner reset fence and
an origin mark. One stationary transition installs the origins; the existing
width sweep installs all inner and outer endpoint markers together.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingMarks

open IntegerMultiplication TM Code
open ChunkControl (Driver)
open StagingControl (Letter)
open StagingProtection (Cell)
open private tape_apply from OAI.Computability.NearSquareRoot.ScheduleStagingBank
open private loaded_plain from OAI.Computability.NearSquareRoot.ScheduleChunkGuardInit

variable {I : Type} (d : Driver)

abbrev J (d : Driver) (I : Type) := Option (StagingOuter.Axis d I)
abbrev W (d : Driver) (I : Type) := Option (J d I)

def inner : W d I → Bool
  | some (some _) => true
  | _ => false

def plain (a : Letter d) : Cell d := Uniform.FenceInit.plain (StagingOuterOutput.plain d a)

def track (deep : Bool) : StagingBank.Track (Uniform.Fence.Symbol (Letter d)) (Cell d) where
  read a := (a.1.1.1,a.2)
  write a v := (((v.1,if deep then v.2 else (false,false)),a.1.2),v.2)

def frame (deep : Bool) : StagingBank.Frame (track d deep) (W d I) where
  offset _ := 0
  enc _ z v := (((v.1,if deep then v.2 else (false,false)),deep && decide (z=0)),v.2)
  read_enc _ _ _ := rfl
  write_enc _ _ _ _ := rfl

def image {Q : Type} (x : Config (Uniform.Fence.Symbol (Letter d)) Q (W d I)) :
    Config (Cell d) (Option Q) (W d I) :=
  ⟨some x.pc,fun j => StagingBank.tape (frame d (inner d j)) j (x.tape j)⟩

def setOrigin (deep : Bool) (a : Cell d) : Cell d := ((a.1.1,deep),a.2)

variable [DecidableEq (Letter d)]

def rule (delimiter : Letter d) : Rule (Cell d) (Option Uniform.FenceInit.Control) (W d I)
  | none, h => some (some (.scan true),fun j => (setOrigin d (inner d j) (h j),.stay))
  | some q, h => (Uniform.FenceInit.rule delimiter none q (fun j => (track d (inner d j)).read (h j))).map
    fun (q',acts) => (some q',fun j => ((track d (inner d j)).write (h j) (acts j).1,(acts j).2))

private theorem advance_image (delimiter : Letter d)
    (x : Config (Uniform.Fence.Symbol (Letter d)) Uniform.FenceInit.Control (W d I)) :
    advance (rule d delimiter) (image d x) =
      (advance (Uniform.FenceInit.rule delimiter none) x).map (image d) := by
  have reads : (fun j => (track d (inner d j)).read (((image d x).tape j).view 0)) =
      fun j => (x.tape j).view 0 := rfl
  simp only [advance,rule,image,Option.map_map] at reads ⊢
  rw [reads]
  cases choice : Uniform.FenceInit.rule delimiter none x.pc (fun j => (x.tape j).view 0) with
  | none => rfl
  | some a =>
    obtain ⟨q,acts⟩ := a
    simp only [Option.map_some,Function.comp_apply,Option.some.injEq,image,Config.mk.injEq,true_and]
    funext j
    exact tape_apply (frame d (inner d j)) j (x.tape j) (acts j)

private theorem image_trace (delimiter : Letter d) {x y : Config _ _ (W d I)} {t}
    (h : Trace (advance (Uniform.FenceInit.rule delimiter none)) x t y) :
    Trace (advance (rule d delimiter)) (image d x) t (image d y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (by rw [advance_image,hs]; rfl) ih

/-- Logical words independently loaded on the covered work tapes. -/
noncomputable def words (s : List Ltr) (i : J d I) : List (Letter d) :=
  match i with
  | some (.inl j) => if j = ChunkDispatch.output (StagingOpen.cmd d) then (s.map Sum.inl).map some else []
  | _ => []

def before (width : List (Letter d)) (ws : J d I → List (Letter d)) :
    Config (Cell d) (Option Uniform.FenceInit.Control) (W d I) :=
  ⟨none,fun i => Tape.loaded (plain d none) ((match i with | none => width | some j => ws j).map (plain d))⟩

omit [DecidableEq (Letter d)] in
private theorem load_view (v : List (Letter d)) (u : ℤ) :
    (Tape.loaded (plain d none) (v.map (plain d))).view u = plain d ((Tape.loaded none v).view u) := by
  cases u <;> simp [Tape.loaded,List.getElem?_map,Option.getD_map]

private theorem origin_step (delimiter : Letter d) (width : List (Letter d)) (ws : J d I → List (Letter d)) :
    advance (rule d delimiter) (before d width ws) = some (image d (ChunkGuard.beforeInit none width ws)) := by
  simp only [advance,rule,before,image,ChunkGuard.beforeInit,Option.map_some,Option.some.injEq,Config.mk.injEq,true_and]
  funext j
  let ls := match j with | none => width | some k => ws k
  change (Tape.loaded (plain d none) (ls.map (plain d))).apply (_,Move.stay) = StagingBank.tape _ j _
  change Tape.mk _ _ = Tape.mk _ _
  rw [Tape.mk.injEq]
  refine ⟨rfl,funext fun u => ?_⟩
  change (if u + 0 = 0 then setOrigin d (inner d j) ((Tape.loaded (plain d none) (ls.map (plain d))).view 0)
    else (Tape.loaded (plain d none) (ls.map (plain d))).view (u+0)) = _
  rw [add_zero,load_view,load_view]
  rw [loaded_plain]
  by_cases eq : u=0
  · subst u
    simp only [ite_true,frame,Tape.loaded,zero_add,decide_true,Bool.and_true]
    cases j with
    | none => rfl
    | some j => cases j <;> rfl
  · cases j with
    | none => simp [eq,ls,frame,inner,plain,StagingOuterOutput.plain,Uniform.FenceInit.plain,Tape.loaded]
    | some j =>
      cases j <;> simp [eq,ls,frame,inner,plain,StagingOuterOutput.plain,Uniform.FenceInit.plain,Tape.loaded]

/-- From all-plain independently loaded tapes, the endpoint is the swept
bank. The width tape returns to zero with all its original data. -/
theorem install (delimiter : Letter d) (first tail : List (Letter d)) (ws : J d I → List (Letter d))
    (hs : delimiter ∉ first) (hb : none ∉ first) (ne : delimiter ≠ none) :
    let width := first ++ delimiter :: tail
    let dst := image d (ChunkGuard.afterInit none width ws first.length)
    Trace (advance (rule d delimiter)) (before d width ws) (4*first.length+7) dst ∧
      advance (rule d delimiter) dst = none := by
  have h := ChunkGuard.initialize_loaded delimiter none first tail ws hs hb ne
  refine ⟨?_,?_⟩
  · convert (Trace.single (origin_step d delimiter _ ws)).trans (image_trace d delimiter h) using 1
    omega
  · rw [advance_image]
    rfl

omit [DecidableEq (Letter d)] in
/-- The completed sweep agrees with every guarded work tape of the staged
candidate, including both markers on its data tape and the outer markers on
the as-yet blank publication tape. The clean shadow stays parked elsewhere. -/
theorem installed {D : Type} (C n : ℕ) (s : List Ltr) (width : List (Letter d)) (i : J d I) :
    (image d (ChunkGuard.afterInit none width (words d s) (StagingProtection.Rpub C n))).tape (some i) =
      (StagingProtection.initial (D:=D) d C n s).tape (some i) := by
  cases i with
  | none =>
    change Tape.mk _ _ = Tape.mk _ _
    rw [Tape.mk.injEq]
    refine ⟨rfl,funext fun u => ?_⟩
    cases u <;> rfl
  | some a =>
    cases a with
    | inr v =>
      change Tape.mk _ _ = Tape.mk _ _
      rw [Tape.mk.injEq]
      refine ⟨rfl,funext fun u => ?_⟩
      cases u <;> rfl
    | inl j =>
      change StagingBank.tape _ _ (Uniform.Fence.markedTape _ _ (Tape.loaded _ _)) =
        Uniform.Fence.markedTape _ _ (StagingReset.markedTape _
          ((StagingControl.entry d (StagingControl.initialBottom d s) .load (Schoolbook.raw s)).tape j))
      rw [StagingControl.entry_input]
      dsimp only
      by_cases eq : j=ChunkDispatch.output (StagingOpen.cmd d)
      · rw [ite_eq_left eq]
        simp only [words,eq,ite_true]
        rfl
      · rw [ite_eq_right eq]
        simp only [words,eq,ite_false]
        rfl

omit [DecidableEq (Letter d)] in
theorem width_parked (R : ℕ) (width : List (Letter d)) (ws : J d I → List (Letter d)) :
    (image d (ChunkGuard.afterInit none width ws R)).tape none =
      Tape.loaded (plain d none) (width.map (plain d)) := by
  change Tape.mk _ _ = Tape.mk _ _
  rw [Tape.mk.injEq]
  refine ⟨rfl,funext fun u => ?_⟩
  change (frame d false (I:=I)).enc none (0+0+u)
    ((Tape.loaded (Uniform.FenceInit.plain none) (width.map Uniform.FenceInit.plain)).view u) = _
  rw [loaded_plain]
  exact (load_view d width u).symm

end StagingMarks

end NearSquareRoot
end Computability
end OAI
