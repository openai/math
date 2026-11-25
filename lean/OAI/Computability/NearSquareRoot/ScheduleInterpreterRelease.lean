import OAI.Computability.NearSquareRoot.ScheduleInterpreterAttempt
import OAI.Computability.NearSquareRoot.ScheduleInterpreterCopy

/-!
# Physical dispatch from a completed attempt to the output tape

A separate output tape is stationary until a trial reports success. On success
a charged transition selects the three-state copy table. A rejected trial halts
with exactly the tapes required for the next slot.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.Release

open IntegerMultiplication TM

variable {A Q I : Type}

abbrev Control (Q : Type) := Q ⊕ Copy.Phase

def active (blank : A) (x : Config A Q I) : Config A (Control Q) (Option I) :=
  ⟨.inl x.pc,(Copy.beginCopy blank x.tape).tape⟩

def copying (x : Config A Copy.Phase (Option I)) : Config A (Control Q) (Option I) :=
  ⟨.inr x.pc,x.tape⟩

def rule (m : Rule A Q I) (ok : Q → Bool) (out : Rule A Copy.Phase (Option I)) :
    Rule A (Control Q) (Option I)
  | .inl q, heads =>
    match m q (fun i => heads (some i)) with
    | some (q',op) => some (.inl q', fun i => match i with
      | none => (heads none,.stay)
      | some j => op j)
    | none => if ok q then some (.inr .seek, fun i => (heads i,.stay)) else none
  | .inr q, heads => (out q heads).map (fun (q',op) => (.inr q',op))

private theorem stay (t : Tape A) : t.apply (t.view 0,.stay) = t := by
  cases t with
  | mk p f =>
    simp [Tape.apply,Move.shift]
    funext k
    split <;> simp_all

private theorem active_step (m : Rule A Q I) (ok : Q → Bool) (out : Rule A Copy.Phase (Option I))
    (blank : A) (x : Config A Q I) :
    advance (rule m ok out) (active blank x) =
      match advance m x with
      | some y => some (active blank y)
      | none => if ok x.pc then some (copying (Copy.beginCopy blank x.tape)) else none := by
  cases h : m x.pc (fun i => (x.tape i).view 0) with
  | none =>
    cases ho : ok x.pc <;> simp [advance, rule, active, Copy.beginCopy, h, ho, copying, stay]
  | some v =>
    obtain ⟨q,o⟩ := v
    simp [advance, rule, active, Copy.beginCopy, h]
    funext i
    cases i with
    | none => exact stay _
    | some => rfl

private theorem copying_step (m : Rule A Q I) (ok : Q → Bool) (out : Rule A Copy.Phase (Option I))
    (x : Config A Copy.Phase (Option I)) :
    advance (rule m ok out) (copying x) = (advance out x).map copying := by
  cases h : out x.pc (fun i => (x.tape i).view 0) with
  | none => simp [advance, rule, copying, h]
  | some z => obtain ⟨q,o⟩ := z; simp [advance, rule, copying, h]

private theorem run_trial (m : Rule A Q I) (ok : Q → Bool) (out : Rule A Copy.Phase (Option I))
    (blank : A) {x y : Config A Q I} {k : ℕ} (h : Trace (advance m) x k y) :
    Trace (advance (rule m ok out)) (active blank x) k (active blank y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (by simp [active_step,hs]) ih

private theorem run_copy (m : Rule A Q I) (ok : Q → Bool) (out : Rule A Copy.Phase (Option I))
    {x y : Config A Copy.Phase (Option I)} {k : ℕ} (h : Trace (advance out) x k y) :
    Trace (advance (rule m ok out)) (copying x) k (copying y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (by simp [copying_step,hs]) ih

theorem rejected (m : Rule A Q I) (ok : Q → Bool) (out : Rule A Copy.Phase (Option I))
    (blank : A) {x y : Config A Q I} {t : ℕ} (h : Trace (advance m) x t y)
    (halt : advance m y = none) (flag : ok y.pc = false) :
    Trace (advance (rule m ok out)) (active blank x) t (active blank y) ∧
      advance (rule m ok out) (active blank y) = none :=
  ⟨run_trial m ok out blank h, by simp [active_step, halt, flag]⟩

theorem accepted (m : Rule A Q I) (ok : Q → Bool) (out : Rule A Copy.Phase (Option I))
    (blank : A) {x y : Config A Q I} {t s : ℕ} (h : Trace (advance m) x t y)
    (halt : advance m y = none) (flag : ok y.pc = true)
    {w : Config A Copy.Phase (Option I)} (copy : Trace (advance out) (Copy.beginCopy blank y.tape) s w)
    (done : advance out w = none) :
    Trace (advance (rule m ok out)) (active blank x) (t+(1+s)) (copying w) ∧
      advance (rule m ok out) (copying w) = none :=
  ⟨(run_trial m ok out blank h).trans (.cons (by simp [active_step, halt, flag]) (run_copy m ok out copy)),
    by simp [copying_step, done]⟩

/-- Along the running trial the output tape only visits its starting cell. -/
theorem work_space (m : Rule A Q I) (ok : Q → Bool) (out : Rule A Copy.Phase (Option I))
    (blank : A) {x y : Config A Q I} {t s : ℕ} (h : Trace (advance m) x t y)
    (hs : VisitsAtMost m x t s) : VisitsAtMost (rule m ok out) (active blank x) t (s+1) := by
  classical
  obtain ⟨cells,cap,cover⟩ := hs
  let embed : (I × ℤ) ↪ (Option I × ℤ) :=
    ⟨fun a => (some a.1,a.2), fun a b h => by cases a; cases b; simpa using h⟩
  refine ⟨insert (none,0) (cells.map embed), (Finset.card_insert_le ..).trans ?_, ?_⟩
  · simpa using Nat.add_le_add_right cap 1
  · intro u hu c tr i
    obtain ⟨z,pre,_⟩ := trace_split h hu
    obtain rfl := trace_endpoint_unique tr (run_trial m ok out blank pre)
    cases i with
    | none => exact Finset.mem_insert_self _ _
    | some i =>
      exact Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨_, cover u hu z pre i, rfl⟩)

private theorem append_space {D P J : Type} {w : Rule D P J}
    {x y : Config D P J} {t n s d : ℕ} (h : Trace (advance w) x t y)
    (pre : VisitsAtMost w x t s) (post : VisitsAtMost w y n d) :
    VisitsAtMost w x (t+n) (s+d) := by
  classical
  obtain ⟨left,capL,L⟩ := pre
  obtain ⟨right,capR,R⟩ := post
  refine ⟨left ∪ right,(Finset.card_union_le ..).trans (Nat.add_le_add capL capR),?_⟩
  intro u hu z run i
  by_cases early : u ≤ t
  · exact Finset.mem_union_left _ (L u early z run i)
  · obtain ⟨w',first,rest⟩ := trace_split run (k := t) (by omega)
    obtain rfl := trace_endpoint_unique h first
    exact Finset.mem_union_right _ (R _ (by omega) z rest i)

private theorem time_space {D P J : Type} [Fintype J] (w : Rule D P J)
    (x : Config D P J) (d : ℕ) :
    VisitsAtMost w x d (Fintype.card J*(2*d+1)) := by
  let lo j := (x.tape j).pos - d
  let hi j := (x.tape j).pos + d
  have h := visitsAtMost_of_tape_fences (m := w) (init := x) (steps := d) lo hi (by
    intro u hu z run i
    have hh := head_excursion run i
    dsimp [lo,hi]
    omega)
  have len (j) : (hi j+1-lo j).toNat = 2*d+1 := by dsimp [lo,hi]; omega
  simpa [len] using h

/-- Bound the running trial by its own visited set. Only the linear-time final
dispatch and copy are charged by their elapsed time in the space estimate. -/
theorem with_copy_space [Fintype I]
    (m : Rule A Q I) (ok : Q → Bool) (out : Rule A Copy.Phase (Option I))
    (blank : A) {x y : Config A Q I} {t s : ℕ} (h : Trace (advance m) x t y)
    (hs : VisitsAtMost m x t s) (d : ℕ) :
    VisitsAtMost (rule m ok out) (active blank x) (t+d)
      (s+1+Fintype.card (Option I)*(2*d+1)) :=
  append_space (run_trial m ok out blank h) (work_space m ok out blank h hs) (time_space _ _ d)

end Uniform.Release

end NearSquareRoot
end Computability
end OAI
