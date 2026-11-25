import OAI.Computability.NearSquareRoot.InterchangeSplitCompose

/-!
# Conditional phase dispatch for a physical scheduler slot

After preparing the workspace, run the trial on the same tapes. Acceptance
halts at the trial's output. A rejected trial passes the tapes to cleanup,
whose halting configuration is the completed retry.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotDispatch

open IntegerMultiplication TM
open TapeSequence (relabel)

variable {A P T C I : Type}

/-- A phase tag changes only finite control. -/
abbrev PC (P T C : Type) := P ⊕ (T ⊕ C)

def accepted (accept : T → Bool) : PC P T C → Bool
  | .inr (.inl q) => accept q
  | _ => false

private def after (trial : Rule A T I) (cleanup : Rule A C I)
    (beginCleanup : C) (accept : T → Bool) : Rule A (T ⊕ C) I
  | .inl q, read =>
    match trial q read with
    | some (r, ops) => some (.inl r, ops)
    | none => if accept q then none else some (.inr beginCleanup, fun i => (read i, .stay))
  | .inr q, read => (cleanup q read).map fun (r, ops) => (.inr r, ops)

def rule (prep : Rule A P I) (trial : Rule A T I) (cleanup : Rule A C I)
    (beginTrial : T) (beginCleanup : C) (accept : T → Bool) : Rule A (PC P T C) I :=
  TapeSequence.rule prep (after trial cleanup beginCleanup accept) (.inl beginTrial)

private theorem liftFenced {Q R : Type} {m : Rule A Q I} {M : Rule A R I} (f : Q → R)
    (step : ∀ x y, advance m x = some y → advance M (relabel f x) = some (relabel f y))
    {lo hi : I → ℤ} {x y t} (run : FencedRun m lo hi x t y) :
    FencedRun M lo hi (relabel f x) t (relabel f y) := by
  have lift {a b s} (h : Trace (advance m) a s b) : Trace (advance M) (relabel f a) s (relabel f b) := by
    induction h with
    | nil => exact .nil _
    | cons h _ ih => exact .cons (step _ _ h) ih
  refine ⟨lift run.1, fun j hj v prefixRun i => ?_⟩
  obtain ⟨w, hw, _⟩ := trace_split run.1 hj
  rw [trace_endpoint_unique prefixRun (lift hw)]
  exact run.2 j hj w hw i

section

variable (prep : Rule A P I) (trial : Rule A T I) (cleanup : Rule A C I)
    (beginTrial : T) (beginCleanup : C) (accept : T → Bool)
local notation "After" => after trial cleanup beginCleanup accept
local notation "Slot" => rule prep trial cleanup beginTrial beginCleanup accept

private theorem trial_advance (x : Config A T I) :
    advance After (relabel Sum.inl x) =
      match advance trial x with
      | some y => some (relabel Sum.inl y)
      | none => if accept x.pc then none else some ⟨Sum.inr beginCleanup, x.tape⟩ := by
  unfold advance
  cases h : trial x.pc (fun i => (x.tape i).view 0) with
  | some a => simp [after,relabel,h]
  | none =>
    cases e : accept x.pc <;> simp [after,relabel,h,e,SM.Action.apply_stay]

private theorem cleanup_advance (x : Config A C I) :
    advance After (relabel Sum.inr x) = (advance cleanup x).map (relabel Sum.inr) := by
  unfold advance
  cases h : cleanup x.pc (fun i => (x.tape i).view 0) <;> simp [after,relabel,h]

/-- Acceptance halts immediately after the trial. The sole extra tick
transfers control from preparation to the trial. -/
theorem run_accept {lo hi : I → ℤ} {x y : Config A P I} {z : Config A T I} {p t : ℕ}
    (pre : FencedRun prep lo hi x p y) (preHalt : advance prep y = none)
    (run : FencedRun trial lo hi ⟨beginTrial,y.tape⟩ t z)
    (stop : advance trial z = none) (ok : accept z.pc = true) :
    FencedRun Slot lo hi (relabel Sum.inl x) (p+1+t) ⟨.inr (.inl z.pc),z.tape⟩ ∧
      advance Slot ⟨.inr (.inl z.pc),z.tape⟩ = none := by
  have r := liftFenced (M := After) Sum.inl
    (fun a b h => by rw [trial_advance, h]) run
  have halt : advance After (relabel Sum.inl z) = none := by rw [trial_advance,stop,ok]; rfl
  exact ⟨TapeSequence.run_fenced _ _ _ pre preHalt r,
    (TapeSequence.run _ _ _ pre.1 preHalt r.1 halt).2⟩

/-- Rejection performs a second handoff to cleanup. All three phases and
both stationary handoff ticks stay inside the same per-tape fence. -/
theorem run_retry {lo hi : I → ℤ} {x y : Config A P I} {z : Config A T I} {w : Config A C I}
    {p t c : ℕ} (pre : FencedRun prep lo hi x p y) (preHalt : advance prep y = none)
    (run : FencedRun trial lo hi ⟨beginTrial,y.tape⟩ t z)
    (stop : advance trial z = none) (retry : accept z.pc = false)
    (clean : FencedRun cleanup lo hi ⟨beginCleanup,z.tape⟩ c w) (cleanHalt : advance cleanup w = none) :
    FencedRun Slot lo hi (relabel Sum.inl x) (p+1+t+1+c) ⟨.inr (.inr w.pc),w.tape⟩ ∧
      advance Slot ⟨.inr (.inr w.pc),w.tape⟩ = none := by
  have r := liftFenced (M := After) Sum.inl
    (fun a b h => by rw [trial_advance, h]) run
  have switched : advance After (relabel Sum.inl z) = some ⟨.inr beginCleanup,z.tape⟩ := by
    rw [trial_advance,stop,retry]; rfl
  have handoff : FencedRun After lo hi (relabel Sum.inl z) 1 ⟨.inr beginCleanup,z.tape⟩ := by
    refine ⟨.single switched,fun j hj v h i => ?_⟩
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · rw [trace_endpoint_unique h (.nil _)]
      exact run.2 t le_rfl z run.1 i
    · rw [trace_endpoint_unique h (.single switched)]
      exact run.2 t le_rfl z run.1 i
  have tail := liftFenced (M := After) Sum.inr
    (fun a b h => by rw [cleanup_advance,h]; rfl) clean
  have endHalt : advance After (relabel Sum.inr w) = none := by rw [cleanup_advance,cleanHalt]; rfl
  have full := (r.trans handoff).trans tail
  rw [show p+1+t+1+c = p+1+(t+1+c) by omega]
  exact ⟨TapeSequence.run_fenced _ _ _ pre preHalt full,
    (TapeSequence.run _ _ _ pre.1 preHalt full.1 endHalt).2⟩

end

end Uniform.SlotDispatch

end NearSquareRoot
end Computability
end OAI
