import OAI.Computability.NearSquareRoot.ScheduleInterpreterFencedRollback
import OAI.Computability.NearSquareRoot.ScheduleInterpreterBudget
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSpace

/-!
# Returning from an unsuccessful physical attempt

The trial and its rollback run on the same heads. A halting control recognized
as a success retains the tentative output. At rejection or timeout, a physical
transition to the eraser restores the original contents and head positions of
all tapes. Only cells visited by this attempt are scanned.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.Restart

open IntegerMultiplication TM

open Rollback (snapshot origins)

variable {A Q I : Type}

abbrev Control (Q I : Type) := Frontier.Control Q I ⊕ Rollback.Control Q I

def active (x : Config (Reset.Cell A A) (Frontier.Control Q I) I) :
    Config (Reset.Cell A A) (Control Q I) I := ⟨.inl x.pc, x.tape⟩

def cleaning (x : Config (Reset.Cell A A) (Rollback.Control Q I) I) :
    Config (Reset.Cell A A) (Control Q I) I := ⟨.inr x.pc, x.tape⟩

private def accepted (ok : Q → Bool) : Frontier.Control Q I → Bool
  | .inl q => ok q
  | .inr _ => false

private def resume : Frontier.Control Q I → Rollback.Control Q I
  | .inl _ => .inr (fun _ => .seekLeft)
  | .inr pending => .inl pending

def rule [Fintype I] (m : Rule A Q I) (ok : Q → Bool) : Rule (Reset.Cell A A) (Control Q I) I
  | .inl pc, r =>
    match Frontier.rule m pc r with
    | some (q',o) => some (.inl q',o)
    | none =>
      if accepted ok pc then none
      else some (.inr (resume pc), fun i => (r i, .stay))
  | .inr pc, r => (Rollback.restoringRule m id pc r).map (fun (q',o) => (.inr q',o))

private theorem stay {D : Type} (t : Tape D) : t.apply (t.view 0, Move.stay) = t := by
  cases t with
  | mk p f =>
    simp [Tape.apply, Move.shift]
    funext k
    split <;> simp_all

private theorem active_step [Fintype I] (m : Rule A Q I) (ok : Q → Bool)
    (x : Config (Reset.Cell A A) (Frontier.Control Q I) I) :
    advance (rule m ok) (active x) =
      match advance (Frontier.rule m) x with
      | some y => some (active y)
      | none => if accepted ok x.pc then none else some (cleaning (Rollback.entry x)) := by
  cases hs : Frontier.rule m x.pc (fun i => (x.tape i).view 0) with
  | none =>
    cases ho : accepted ok x.pc <;>
      simp [advance, rule, active, hs, cleaning, stay, ho]
    exact ⟨rfl,rfl⟩
  | some z =>
    obtain ⟨q,o⟩ := z
    simp [active, advance, rule, hs]

private theorem cleaning_step [Fintype I] (m : Rule A Q I) (ok : Q → Bool)
    (x : Config (Reset.Cell A A) (Rollback.Control Q I) I) :
    advance (rule m ok) (cleaning x) = (advance (Rollback.restoringRule m id) x).map cleaning := by
  cases h : Rollback.restoringRule m id x.pc (fun i => (x.tape i).view 0) with
  | none => simp [advance, cleaning, rule, h]
  | some z => obtain ⟨q,o⟩ := z; simp [advance, cleaning, rule, h]

private theorem run_active [Fintype I] (m : Rule A Q I) (ok : Q → Bool)
    {x y : Config (Reset.Cell A A) (Frontier.Control Q I) I} {t : ℕ}
    (h : Trace (advance (Frontier.rule m)) x t y) :
    Trace (advance (rule m ok)) (active x) t (active y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (by simp [active_step, hs]) ih

private theorem run_cleaning [Fintype I] (m : Rule A Q I) (ok : Q → Bool)
    {x y : Config (Reset.Cell A A) (Rollback.Control Q I) I} {t : ℕ}
    (h : Trace (advance (Rollback.restoringRule m id)) x t y) :
    Trace (advance (rule m ok)) (cleaning x) t (cleaning y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (by simp [cleaning_step, hs]) ih

def start (x : Config A Q I) :=
  active (Frontier.config (snapshot x) (origins x) (origins x) (origins x) x)

def retry (x : Config A Q I) := cleaning (Q := Q) (Rollback.restored id (snapshot x) (origins x))

/-- A caller can restart with one finite-control change: after an unsuccessful
attempt even volatile data, scratch head locations, and the frontier markers
are identical to their values at entry. -/
theorem retry_tapes (x : Config A Q I) : (retry x).tape = (start x).tape :=
  Rollback.restored_tapes x

/-- The time bound covers simulated writes, frontier maintenance, dispatch
and restoration. A successful trial halts while its product is still present. -/
theorem finish [Fintype I] (m : Rule A Q I) (ok : Q → Bool)
    {x y : Config A Q I} {k : ℕ} (run : Trace (advance m) x k y) (stop : advance m y = none) :
    ∃ l r t w, (∀ i, l i ≤ (x.tape i).pos ∧ (x.tape i).pos ≤ r i ∧
      l i ≤ (y.tape i).pos ∧ (y.tape i).pos ≤ r i ∧ r i - l i ≤ (k : ℤ)) ∧
      t ≤ 5*k+4 ∧ Trace (advance (rule m ok)) (start x) t w ∧
      advance (rule m ok) w = none ∧
      w = if ok y.pc then active (Frontier.config (snapshot x) (origins x) l r y) else retry x := by
  obtain ⟨l,r,tr,interval⟩ := Frontier.simulate_trace m (snapshot x) (origins x) (origins x) (origins x) run
    (fun _ => ⟨le_rfl,le_rfl⟩)
  simp only [sub_self, zero_add] at interval
  let z := Frontier.config (snapshot x) (origins x) l r y
  have hz : advance (Frontier.rule m) z = none := (Frontier.halt_iff ..).2 stop
  have hr : Trace (advance (rule m ok)) (start x) (2*k) (active z) := run_active m ok tr
  cases hok : ok y.pc with
  | true =>
    exact ⟨l,r,2*k,active z,interval,by omega,hr,by rw [active_step, hz]; change (if ok y.pc then _ else _) = _; simp [hok],
      by simp [z]⟩
  | false =>
    obtain ⟨j,_,u,_,ht₁,ht₂,cleanup,hh,bound⟩ := Rollback.timeout_restore m id (snapshot x)
      (origins x) x (fun _ => rfl) (fun _ _ => rfl) tr
    have first : advance (rule m ok) (active z) = some (cleaning (Rollback.entry z)) := by
      rw [active_step, hz]
      change (if ok y.pc then _ else _) = _
      simp [hok]
    refine ⟨l,r,2*k+(1+u),retry x,interval,by omega,hr.trans (.cons first (run_cleaning m ok cleanup)),?_,?_⟩
    · exact (cleaning_step m ok _).trans (by simp [hh])
    · simp

private theorem invariant {D : Type} {f : D → Option D} (P : D → Prop)
    (next : ∀ {u v}, P u → f u = some v → P v) {u v : D} {k : ℕ}
    (h : Trace f u k v) (initial : P u) : P v := by
  induction h with
  | nil => exact initial
  | cons hs _ ih => exact ih (next initial hs)

/-- The combined dispatch, including rollback, never crosses a fence that
confines the underlying trial. -/
theorem stays_within [Fintype I] (m : Rule A Q I) (ok : Q → Bool) (x : Config A Q I)
    (lo hi : I → ℤ)
    (fits : ∀ {j z}, Trace (advance m) x j z → ∀ i, lo i ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ hi i)
    {w : Config (Reset.Cell A A) (Control Q I) I} {t : ℕ}
    (run : Trace (advance (rule m ok)) (start x) t w) :
    ∀ i, lo i ≤ (w.tape i).pos ∧ (w.tape i).pos ≤ hi i := by
  let init := Frontier.config (snapshot x) (origins x) (origins x) (origins x) x
  let P (z : Config (Reset.Cell A A) (Control Q I) I) :=
    ∃ n u, Trace (advance (Frontier.rule m)) init n u ∧
      (z = active u ∨ ∃ d v, Trace (advance (Rollback.restoringRule m id)) (Rollback.entry u) d v ∧
        z = cleaning v)
  have hstart : P (start x) := ⟨0, init, .nil _, .inl rfl⟩
  have hp : P w := by
    refine invariant P ?_ run hstart
    rintro z w ⟨n,u,tr,rfl | ⟨d,v,cl,rfl⟩⟩ hs
    · rw [active_step] at hs
      cases hu : advance (Frontier.rule m) u with
      | some u' => exact ⟨_,u',tr.trans (.single hu),.inl (by simpa [hu] using hs.symm)⟩
      | none =>
        cases hok : accepted ok u.pc with
        | true => simp [hu, hok] at hs
        | false =>
          exact ⟨n,u,tr,.inr ⟨0,_,.nil _,by simpa [hu, hok] using hs.symm⟩⟩
    · rw [cleaning_step] at hs
      cases hv : advance (Rollback.restoringRule m id) v with
      | none => simp [hv] at hs
      | some v' =>
        exact ⟨n,u,tr,.inr ⟨_,v',cl.trans (.single hv),by simpa [hv] using hs.symm⟩⟩
  obtain ⟨n,u,tr,rfl | ⟨d,v,cl,rfl⟩⟩ := hp
  · exact Rollback.timeout_prefix_restore m id (snapshot x) (origins x) lo hi x
      (fun _ => rfl) fits tr (.nil _)
  · exact Rollback.timeout_prefix_restore m id (snapshot x) (origins x) lo hi x
      (fun _ => rfl) fits tr cl

/-- Even when only the cardinal space bound on the underlying halting trial
is known, rollback has a fixed linear-space allowance about the same heads. -/
theorem visits [Fintype I] (m : Rule A Q I) (ok : Q → Bool)
    {x y : Config A Q I} {t space : ℕ} (run : Trace (advance m) x t y)
    (halt : advance m y = none) (budget : VisitsAtMost m x t space) (k : ℕ) :
    VisitsAtMost (rule m ok) (start x) k (Fintype.card I * (2*space+1)) := by
  let lo i := (x.tape i).pos - space
  let hi i := (x.tape i).pos + space
  have h := visitsAtMost_of_tape_fences (m := rule m ok) (init := start x) (steps := k) lo hi
    (fun _ _ _ h => stays_within m ok x lo hi (fun sub i =>
      radius_of_visits budget (before_halt run halt sub) sub i) h)
  have len (i) : (hi i + 1 - lo i).toNat = 2*space+1 := by dsimp [hi,lo]; omega
  simpa [len] using h

/-- The endpoint markers in a successful return are within the space radius
of its own attempt. This bounds the final scans even when the lookup clock is
far longer than the input. -/
theorem endpoint_radius {m : Rule (Reset.Cell A A) (Control Q I) I}
    (x y : Config A Q I) (l r : I → ℤ) {t s : ℕ}
    (run : Trace (advance m) (start x) t (active (Frontier.config (snapshot x) (origins x) l r y)))
    (space : VisitsAtMost m (start x) t s) (i : I) :
    (x.tape i).pos-s ≤ l i ∧ r i ≤ (x.tape i).pos+s := by
  have key (p : ℤ) (h : p ≠ (x.tape i).pos →
      ((active (Frontier.config (snapshot x) (origins x) l r y)).tape i).absolute p ≠
        ((start x).tape i).absolute p) :
      (x.tape i).pos-s ≤ p ∧ p ≤ (x.tape i).pos+s := by
    by_cases he : p = (x.tape i).pos
    · omega
    · exact changed_in_radius space run i p (h he)
  refine ⟨(key (l i) ?_).1,(key (r i) ?_).2⟩
  · intro he h
    have z := congrArg Reset.Cell.leftEnd h
    simp [active, start, Frontier.config, Frontier.tape, Tape.absolute, origins] at z
    omega
  · intro he h
    have z := congrArg Reset.Cell.rightEnd h
    simp [active, start, Frontier.config, Frontier.tape, Tape.absolute, origins] at z
    omega

end Uniform.Restart

end NearSquareRoot
end Computability
end OAI
