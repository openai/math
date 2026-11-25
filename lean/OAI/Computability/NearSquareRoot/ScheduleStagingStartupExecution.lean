import OAI.Computability.NearSquareRoot.ScheduleStagingStartupRun
import OAI.Computability.NearSquareRoot.ScheduleStagingStartupReject

/-! # Physical execution from unmarked public input

A completed initialization can be followed by an arbitrary staged machine.
Actual halting traces reflect to the post-initialization machine. Their public
output is the same complete tape at the routed output address.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingStartup

open IntegerMultiplication TM Code Bits CommonAlphabet CommonAlphabet.Pipeline
open ChunkControl (Driver)
open StagingProtection (Cell Tapes)
open private second_step from OAI.Computability.NearSquareRoot.InterchangeSplitCompose

variable {I P Q A : Type} (d : Driver)

def expose (src wd : Tape A) (x : Config A Q I) : Config A (P ⊕ Q) (Index I) :=
  ⟨.inr x.pc,store src wd x.tape⟩

private theorem expose_step (m : Rule A P (Index I)) (n : Rule A Q I) (q : Q)
    (src wd : Tape A) (x : Config A Q I) :
    advance (TapeSequence.rule m ((coreRoute I).rule n) q) (expose src wd x) =
      (advance n x).map (expose src wd) := by
  let bg := store src wd x.tape
  have eq (v : Config A Q I) : TapeSequence.relabel (T:=P ⊕ Q) Sum.inr (mapper (coreRoute I) bg v) =
      expose src wd v := by
    change Config.mk _ _ = Config.mk _ _
    rw [Config.mk.injEq]
    exact ⟨rfl,core_store ..⟩
  rw [← eq x,second_step,mapped_step,Option.map_map]
  exact congrArg (fun f => (advance n x).map f) (funext eq)

private theorem expose_trace (m : Rule A P (Index I)) (n : Rule A Q I) (q : Q)
    (src wd : Tape A) {x y : Config A Q I} {u : ℕ} (run : Trace (advance n) x u y) :
    Trace (advance (TapeSequence.rule m ((coreRoute I).rule n) q)) (expose src wd x) u (expose src wd y) := by
  induction run with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (by rw [expose_step,hs]; rfl) ih

private theorem expose_reflect (m : Rule A P (Index I)) (n : Rule A Q I) (q : Q)
    (src wd : Tape A) {x : Config A Q I} {y u}
    (run : Trace (advance (TapeSequence.rule m ((coreRoute I).rule n) q)) (expose src wd x) u y) :
    ∃ v, Trace (advance n) x u v ∧ y = expose src wd v := by
  generalize eq : expose (P:=P) src wd x = a at run
  induction run generalizing x with
  | nil => exact ⟨x,.nil _,eq.symm⟩
  | @cons a b c t h _ ih =>
    subst a
    rw [expose_step] at h
    cases hx : advance n x with
    | none => simp [hx] at h
    | some v =>
      obtain ⟨w,tail,hw⟩ := ih (by simpa [hx] using h)
      exact ⟨w,.cons hx tail,hw⟩

variable [DecidableEq I] [DecidableEq (StagingControl.Letter d)]

omit [DecidableEq I] [DecidableEq (StagingControl.Letter d)] in
theorem initialMachine_eq (k C : ℕ) (x y : Word) :
    initialMachine (I:=I) (Q:=Q) d k C x y =
      initialConfig (Sum.inl (start k)) (.inl false) (StagingProtection.bit d)
        (StagingSerialize.put d .sep) (StagingProtection.blank d) x y := rfl

noncomputable def staged (q : Q) (C n : ℕ) (s : List Ltr) : Config (Cell d) Q (Tapes d I) :=
  ⟨q,(StagingProtection.initial (D:=Unit) d C n s).tape⟩

abbrev active (C : ℕ) (p : ChunkTask.Input) (v : Config (Cell d) Q (Tapes d I)) :
    Config (Cell d) (PC p.k (StagingWidth.Phase C) ⊕ Q) (Axis d I) :=
  expose (sourceAt d p.x p.y) (StagingWidth.widthTape d C p.n) v

/-- Finite control reaches the configured candidate from the literal two
operands, with no preloaded table, split, radius, or initialized mark tape. -/
theorem launch (C : ℕ) (p : ChunkTask.Input) (post : Rule (Cell d) Q (Tapes d I)) (q : Q) :
    ∃ t ≤ budget C p.n + 1, Trace (advance (machine d p.k C post q))
      (initialMachine d p.k C p.x p.y) t (active d C p (staged d q C p.n (ChunkPhases.input p))) := by
  obtain ⟨t,ht,h,stop⟩ := prepares (I:=I) d C p
  have first := TapeSequence.first_trace _ ((coreRoute _).rule post) q h
  have jump := TapeSequence.handoff _ ((coreRoute _).rule post) q stop
  exact ⟨t+1,by omega,first.trans (.single jump)⟩

/-- The source program's clock plus the common linear initialization cost
suffice for the ordinary one-input-tape machine. -/
theorem execute (C : ℕ) (p : ChunkTask.Input) (post : Rule (Cell d) Q (Tapes d I)) (q : Q)
    {t z} (run : Trace (advance post) (staged d q C p.n (ChunkPhases.input p)) t z)
    (halt : advance post z = none) :
    ∃ u ≤ budget C p.n+1+t, Trace (advance (machine d p.k C post q))
      (initialMachine d p.k C p.x p.y) u (active d C p z) ∧
      advance (machine d p.k C post q) (active d C p z) = none := by
  obtain ⟨s,hs,init⟩ := launch d C p post q
  refine ⟨_,by omega,init.trans (expose_trace _ _ _ _ _ run),?_⟩
  rw [machine,active,expose_step,halt]
  rfl

/-- Every actual halt on legal input is a halt of the underlying candidate
on the correctly serialized and fenced instance. -/
theorem reflect (C : ℕ) (p : ChunkTask.Input) (post : Rule (Cell d) Q (Tapes d I)) (q : Q)
    {u y} (run : Trace (advance (machine d p.k C post q)) (initialMachine d p.k C p.x p.y) u y)
    (halt : advance (machine d p.k C post q) y = none) :
    ∃ t ≤ u, ∃ z, Trace (advance post) (staged d q C p.n (ChunkPhases.input p)) t z ∧
      advance post z = none ∧ y = active d C p z := by
  obtain ⟨s,_,init⟩ := launch d C p post q
  have le := Uniform.before_halt run halt init
  obtain ⟨mid,front,tail⟩ := trace_split run le
  rw [trace_endpoint_unique front init] at tail
  obtain ⟨z,orig,eq⟩ := expose_reflect _ post q _ _ tail
  rw [eq] at halt
  have stop : advance post z = none := by simpa only [machine,expose_step,Option.map_eq_none_iff] using halt
  exact ⟨_,Nat.sub_le ..,z,orig,stop,eq⟩

/-- On a fitting split the startup uses a fixed linear clock. Subsequently
the held input and width heads stay fixed, so the supplied head bound for
the candidate covers every remaining transition even on nonhalting attempts. -/
theorem prefix_fit (C : ℕ) (p : ChunkTask.Input) (post : Rule (Cell d) Q (Tapes d I)) (q : Q)
    (bound : ∀ {a v}, Trace (advance post) (staged d q C p.n (ChunkPhases.input p)) a v →
      ∀ i, -(StagingProtection.Rpub C p.n : ℤ) ≤ (v.tape i).pos ∧ (v.tape i).pos ≤ StagingProtection.Rpub C p.n)
    {u y} (run : Trace (advance (machine d p.k C post q)) (initialMachine d p.k C p.x p.y) u y)
    (i : Axis d I) : -((budget C p.n+1 : ℕ) : ℤ) ≤ (y.tape i).pos ∧ (y.tape i).pos ≤ budget C p.n+1 := by
  obtain ⟨s,hs,init⟩ := launch d C p post q
  by_cases h : u ≤ s
  · obtain ⟨lo,hi⟩ := head_excursion run i
    have pos : ((initialMachine (Q:=Q) d p.k C p.x p.y).tape i).pos = 0 := rfl
    rw [pos] at lo hi
    omega
  · obtain ⟨mid,front,tail⟩ := trace_split run (k:=s) (by omega)
    rw [trace_endpoint_unique front init] at tail
    obtain ⟨z,hz,rfl⟩ := expose_reflect _ post q _ _ tail
    have sizes : StagingProtection.Rpub C p.n + p.n ≤ budget C p.n := by
      unfold StagingProtection.Rpub StagingOuter.radius budget
      nlinarith
    rcases i with (_|_)|i
    · change -((budget C p.n+1 : ℕ) : ℤ) ≤ (p.n : ℤ) ∧ (p.n : ℤ) ≤ budget C p.n+1
      omega
    · change -((budget C p.n+1 : ℕ) : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ budget C p.n+1
      omega
    · have := bound hz i
      change -((budget C p.n+1 : ℕ) : ℤ) ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ budget C p.n+1
      omega

end StagingStartup

end NearSquareRoot
end Computability
end OAI
