import OAI.Computability.NearSquareRoot.ScheduleStagingReach
import OAI.Computability.NearSquareRoot.ScheduleChunkWholeOutput

/-! # An unconditional outer space bound for staged candidate attempts

The fixed rule guards all transitions, including digit calls and publication.
The shadow of its designated raw output has no outer fence symbols, even on
the unused cells outside the answer. Both protections operate in parallel with
the attempted transition and add no steps to a successful run.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingProtection

open IntegerMultiplication TM Code Bits
open StagingOuter (Axis Letter)
open ChunkControl (Driver)
open ChunkTask ChunkLoop ChunkPhases

noncomputable section

abbrev Cell (d : Driver) := Uniform.Fence.Symbol (Letter d)
abbrev State (d : Driver) (D : Type) := Bool × Option (StagingControl.State d ⊕ D)
abbrev Tapes (d : Driver) (I : Type) := Option (Option (Axis d I))

def Rpub (C n : ℕ) := StagingOuter.radius C n

variable {I D : Type} (d : Driver)

def blank : Cell d := Uniform.FenceInit.plain (StagingOuterOutput.blank d)

def bit (b : Bool) : Cell d := Uniform.FenceInit.plain (StagingOuterOutput.bit d b)

def clean (a : Cell d) : Cell d := Uniform.FenceInit.plain a.1

local instance axisFintype [Finite I] : Fintype (Axis d I) := Fintype.ofFinite _

variable [DecidableEq I] [Finite I]

def rule (digit : Rule (Letter d) D (Axis d I)) (start : D) :
    Rule (Cell d) (State d D) (Tapes d I) :=
  ChunkWhole.Mirror.rule (clean d) none (Uniform.Fence.guard (StagingOuterOutput.rule d digit start))

/-- The source stream is arbitrary. Its symbols may describe a malformed
candidate. The input and workspace heads all begin at address zero. -/
def unmarked (C n : ℕ) (s : List Ltr) :=
  StagingPublish.active (StagingOuterOutput.blank d)
    (StagingCycle.controller (D:=D) (StagingOuter.config (I:=I) d (StagingOuter.radius C n)
      (StagingControl.entry d (StagingControl.initialBottom d s) .load (Schoolbook.raw s))))

def initial (C n : ℕ) (s : List Ltr) : Config (Cell d) (State d D) (Tapes d I) :=
  ChunkWhole.Mirror.pack (clean d) none (Uniform.Fence.marked (ChunkGuard.left (Rpub C n))
    (ChunkGuard.right (Rpub C n)) false (unmarked (D:=D) (I:=I) d C n s))

omit [DecidableEq I] [Finite I] in
theorem unmarked_pos (C n : ℕ) (s : List Ltr) (i : Option (Axis d I)) :
    ((unmarked (D:=D) d C n s).tape i).pos = 0 := by
  cases i with
  | none => rfl
  | some j =>
    cases j with
    | inl j =>
      change (((StagingControl.entry d (StagingControl.initialBottom d s) .load (Schoolbook.raw s)).tape j)).pos = 0
      rw [StagingControl.entry_input]
      dsimp only
      split <;> rfl
    | inr => rfl

omit [DecidableEq I] [Finite I] in
/-- The shadow tape is initially entirely blank, including the two guard
addresses. -/
theorem initial_output (C n : ℕ) (s : List Ltr) :
    ((initial (I:=I) (D:=D) d C n s).tape none) = Tape.loaded (blank d) [] := by
  change Tape.mk _ _ = Tape.mk _ _
  congr 1
  funext p
  cases p <;> rfl

/-- Every prefix of every attempted program stays within the same radius.
The program need not terminate or satisfy a functional specification. -/
theorem prefix_within (C n : ℕ) (s : List Ltr) (digit : Rule (Letter d) D (Axis d I)) (start : D)
    {u : ℕ} {z} (h : Trace (advance (rule d digit start)) (initial d C n s) u z)
    (i : Tapes d I) : -(Rpub C n : ℤ) ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ Rpub C n := by
  let x := unmarked (D:=D) (I:=I) d C n s
  let lo := ChunkGuard.left (J:=Option (Axis d I)) (Rpub C n)
  let hi := ChunkGuard.right (J:=Option (Axis d I)) (Rpub C n)
  let m := StagingOuterOutput.rule d digit start
  have hx : Uniform.Fence.within lo hi x := by
    intro i
    simp [x,unmarked_pos,lo,hi,ChunkGuard.left,ChunkGuard.right]
  obtain ⟨y,hy,rfl⟩ := ChunkWhole.Mirror.reflect (clean d) none (Uniform.Fence.guard m) h
  obtain ⟨v,tag,hv,rfl⟩ := Uniform.Fence.trace_within m lo hi hx hy
  cases i with
  | none => exact hv none
  | some j => exact hv j

/-- A halting attempt with a clear abort flag reflects an entire halting
execution of the underlying staged rule, at precisely the same step count. -/
theorem reflect_success (C n : ℕ) (s : List Ltr) (digit : Rule (Letter d) D (Axis d I))
    (start : D) {t : ℕ} {y}
    (run : Trace (advance (rule d digit start)) (initial d C n s) t y)
    (ok : y.pc.1 = false) (halt : advance (rule d digit start) y = none) :
    let lo := ChunkGuard.left (J:=Option (Axis d I)) (Rpub C n)
    let hi := ChunkGuard.right (J:=Option (Axis d I)) (Rpub C n)
    ∃ z, y = ChunkWhole.Mirror.pack (clean d) none (Uniform.Fence.marked lo hi false z) ∧
      FencedRun (StagingOuterOutput.rule d digit start) lo hi (unmarked d C n s) t z ∧
      advance (StagingOuterOutput.rule d digit start) z = none := by
  let m := StagingOuterOutput.rule d digit start
  let lo := ChunkGuard.left (J:=Option (Axis d I)) (Rpub C n)
  let hi := ChunkGuard.right (J:=Option (Axis d I)) (Rpub C n)
  dsimp only
  have hx : Uniform.Fence.within lo hi (unmarked (D:=D) d C n s) := by
    intro i
    simp [unmarked_pos,lo,hi,ChunkGuard.left,ChunkGuard.right]
  obtain ⟨y,hy,rfl⟩ := ChunkWhole.Mirror.reflect (clean d) none (Uniform.Fence.guard m) run
  have stopped : advance (Uniform.Fence.guard m) y = none := by
    simpa only [rule,ChunkWhole.Mirror.advance_pack,Option.map_eq_none_iff,m] using halt
  obtain ⟨z,rfl,exec,stop⟩ := Uniform.Fence.reflect_halt m lo hi hx hy ok stopped
  refine ⟨z,rfl,⟨exec,?_⟩,stop⟩
  intro u hu v hv i
  obtain ⟨mid,head,tail⟩ := trace_split hy hu
  obtain ⟨orig,flag,inside,rfl⟩ := Uniform.Fence.trace_within m lo hi hx head
  have hflag := (Uniform.Fence.reflect_trace m lo hi inside tail rfl).1
  subst flag
  obtain ⟨_,orig',inside',_,pre⟩ := Uniform.Fence.reflect_trace m lo hi hx head rfl
  rw [trace_endpoint_unique hv pre]
  exact inside' i

/-- A concrete finite common cover for any time cutoff and any input stream,
with a radius depending only on the installed controller and the input length. -/
theorem visited (C n budget : ℕ) (s : List Ltr) (digit : Rule (Letter d) D (Axis d I))
    (start : D) : VisitsAtMost (rule d digit start) (initial d C n s) budget
      (Nat.card (Tapes d I) * (2*Rpub C n+1)) := by
  have h := visitsAtMost_of_common_fence (m:=rule d digit start) (init:=initial d C n s) (steps:=budget)
    (-(Rpub C n : ℤ)) (Rpub C n : ℤ) (fun _ _ _ ht i => prefix_within d C n s digit start ht i)
  rw [Nat.card_eq_fintype_card]
  convert h using 2
  omega

/-- The common space constant depends only on the fixed controller and
the bound on the number of digit tapes. This covers length zero as well. -/
theorem visited_linear (K C n budget : ℕ) (s : List Ltr) (digit : Rule (Letter d) D (Axis d I))
    (start : D) (size : Nat.card I ≤ K) :
    VisitsAtMost (rule d digit start) (initial d C n s) budget
      (((Nat.card (StagingControl.Axis d)+K+3)*(8*(C+50)+1))*(n+1)) := by
  obtain ⟨cells,count,cover⟩ := visited d C n budget s digit start
  refine ⟨cells,count.trans ?_,cover⟩
  have card : Nat.card (Tapes d I) ≤ Nat.card (StagingControl.Axis d)+K+3 := by
    change Nat.card (Option (Option (StagingControl.Axis d ⊕ Option I))) ≤ _
    rw [Finite.card_option,Finite.card_option,Nat.card_sum,Finite.card_option (α:=I)]
    omega
  have span : 2*Rpub C n+1 ≤ (8*(C+50)+1)*(n+1) := by
    unfold Rpub StagingOuter.radius
    nlinarith
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul card span

/-- A successful fitting run takes the same number of transitions, returns
with its abort flag clear and leaves an exact complete word on the clean tape. -/
theorem success (C : ℕ) (p : Input) (w : Word)
    (digit : Rule (Letter d) D (Axis d I)) (start : D) {t : ℕ} {z}
    (tr : FencedRun (StagingOuterOutput.rule d digit start)
      (fun _ => -(StagingOuter.radius C p.n : ℤ))
      (fun _ => (StagingOuter.radius C p.n : ℤ))
      (StagingOuterOutput.initial d C p) t z)
    (halt : advance (StagingOuterOutput.rule d digit start) z = none)
    (out : whole (StagingOuterOutput.blank d) (w.map (StagingOuterOutput.bit d)) (z.tape none)) :
    ∃ y, Trace (advance (rule d digit start)) (initial d C p.n (input p)) t y ∧
      advance (rule d digit start) y = none ∧ y.pc.1 = false ∧
      whole (blank d) (w.map (bit d)) (y.tape none) := by
  let m := StagingOuterOutput.rule d digit start
  let lo := ChunkGuard.left (J:=Option (Axis d I)) (Rpub C p.n)
  let hi := ChunkGuard.right (J:=Option (Axis d I)) (Rpub C p.n)
  have fits {u v} (hu : u ≤ t) (hv : Trace (advance m) (StagingOuterOutput.initial d C p) u v) :
      Uniform.Fence.within lo hi v := by
    exact tr.2 u hu v hv
  let marked := Uniform.Fence.marked lo hi false z
  have guarded := Uniform.Fence.trace_marked m lo hi tr.1 fits
  have stopped : advance (Uniform.Fence.guard m) marked = none := by
    simp only [marked,Uniform.Fence.advance_marked m lo hi z (fits le_rfl tr.1),halt,Option.map_none,m]
  let plain := Uniform.FenceInit.plain (A:=Letter d)
  have result := ChunkWhole.Mirror.whole plain (StagingOuterOutput.blank d)
    (w.map (StagingOuterOutput.bit d)) (marked.tape none) out
  refine ⟨_,ChunkWhole.Mirror.run (clean d) none (Uniform.Fence.guard m) guarded,?_,rfl,?_⟩
  · rw [rule,ChunkWhole.Mirror.advance_pack,stopped]
    rfl
  · change whole (plain (StagingOuterOutput.blank d)) (w.map (fun b => plain (StagingOuterOutput.bit d b)))
      (ChunkWhole.Mirror.tape (fun a => plain a.1) (marked.tape none))
    simpa only [List.map_map,Function.comp_def] using result

/-- The guarded, mirrored program implements a promised successful staged call
on a count-independent finite number of tapes. -/
theorem run (C : ℕ) (m : Operands → Word) (p : Input) (w : Word) (hw : w.length = 2*p.n)
    (digit : Rule (Letter d) D (Axis d I)) (start : D) {T : ℕ}
    (ctl : StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p (w.map Ltr.bit))
    (width : ∀ i < p.count, (digitReply m p i).length = 2*p.u)
    (call : ∀ i < p.count, StagingOuter.Call d C m p digit start T i) :
    ∃ t ≤ (p.count+1)*(6*(C*(p.n+1))+T+8)+1+2*p.n, ∃ z,
      Trace (advance (rule d digit start)) (initial d C p.n (input p)) t z ∧
      advance (rule d digit start) z = none ∧ z.pc.1 = false ∧
      whole (blank d) (w.map (bit d)) (z.tape none) := by
  obtain ⟨t,ht,z,tr,halt,out⟩ := StagingOuterOutput.run_fixed_radius d C m p w hw digit start ctl width call
  exact ⟨t,by omega,success d C p w digit start tr halt out⟩

end
end StagingProtection

end NearSquareRoot
end Computability
end OAI
