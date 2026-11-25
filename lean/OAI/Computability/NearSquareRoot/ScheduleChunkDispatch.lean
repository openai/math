import OAI.Computability.NearSquareRoot.ScheduleSchoolIO
import OAI.Computability.NearSquareRoot.ShortWordSpace

/-!
# Finite phase control around a shared stack compiler

Each phase runs one command on the same data registers. On return to the
empty control stack, one transition can select a phase and consume a test bit.
The phase label costs no simulated steps inside a command, and the stacks at
every prefix coincide with those of the underlying compiled command.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkDispatch

open IntegerMultiplication IntegerMultiplication.Code

variable {F : Type} [Fintype F] (cmd : F → Cmd)

noncomputable def area : List (Prog.Loc Ltr) :=
  Finset.univ.toList.flatMap (fun f => Prog.sites [] (cmd f))

instance : Finite (Prog.Ptr (area cmd)) := by
  classical
  exact (Fintype.subtype (area cmd).toFinset (by simp)).finite

instance : Finite (Prog.Idx (area cmd)) := by
  classical
  exact (Fintype.subtype (Prog.used (area cmd)).toFinset (by simp)).finite

theorem good (f : F) : Prog.Good (area cmd) [] (cmd f) := by
  intro l hl
  exact List.mem_flatMap.mpr ⟨f, by simp, hl⟩

def entry (f : F) : Prog.Pc (area cmd) := some ⟨([], cmd f), good cmd f (Prog.sites_self _ _)⟩

def output : Prog.Ix (area cmd) := some ⟨0, by simp [Prog.used]⟩

abbrev Control := F × Prog.Pc (area cmd)
abbrev Base := SM.Config (Prog.Sym (area cmd)) (Prog.Pc (area cmd)) (Prog.Ix (area cmd))
abbrev Config := SM.Config (Prog.Sym (area cmd)) (Control cmd) (Prog.Ix (area cmd))

/-- A successful branch gives its destination and whether it consumes the top
letter of register zero. A missing branch halts the whole machine. -/
abbrev Route := F → (Prog.Ix (area cmd) → Option (Prog.Sym (area cmd))) → Option (F × Bool)

def wrap (f : F) (x : Base cmd) : Config cmd := ⟨(f, x.pc), x.stack⟩

noncomputable def rule (route : Route cmd) :
    SM.Rule (Prog.Sym (area cmd)) (Control cmd) (Prog.Ix (area cmd)) := by
  classical
  exact fun (f, q) stk =>
    match Prog.compile (area cmd) q stk with
    | some (q', acts) => some ((f, q'), acts)
    | none =>
      match q, stk none with
      | none, none => (route f stk).map fun (g, pop) =>
          ((g, entry cmd g), if pop then Function.update (fun _ => .skip) (output cmd) .pop
                               else fun _ => .skip)
      | _, _ => none

def start (f : F) : Control cmd := (f, entry cmd f)

noncomputable def beginPhase (f : F) (r : Reg Ltr) : Config cmd :=
  wrap cmd f (Prog.machine (area cmd) (entry cmd f) r [])

noncomputable def endPhase (f : F) (r : Reg Ltr) : Config cmd :=
  wrap cmd f (Prog.machine (area cmd) none r [])

variable (route : Route cmd)

theorem lift_one (f : F) {x y : Base cmd}
    (h : SM.advance (Prog.compile (area cmd)) x = some y) :
    SM.advance (rule cmd route) (wrap cmd f x) = some (wrap cmd f y) := by
  classical
  cases hc : Prog.compile (area cmd) x.pc (SM.tops x) with
  | none => simp [SM.advance, hc] at h
  | some pair =>
    obtain ⟨q, acts⟩ := pair
    simp only [SM.advance, hc, Option.map_some, Option.some.injEq] at h
    subst y
    change (match Prog.compile (area cmd) x.pc (SM.tops x) with
      | some (q', acts) => some ((f, q'), acts)
      | none => _).map _ = _
    rw [hc]
    rfl

theorem lift_run (f : F) {x y : Base cmd} {t : ℕ}
    (h : Trace (SM.advance (Prog.compile (area cmd))) x t y) :
    Trace (SM.advance (rule cmd route)) (wrap cmd f x) t (wrap cmd f y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (lift_one cmd route f h) ih

theorem prefix_iff (f : F) {x y : Base cmd} {t k : ℕ}
    (h : Trace (SM.advance (Prog.compile (area cmd))) x t y) (hk : k ≤ t) (z : Config cmd) :
    Trace (SM.advance (rule cmd route)) (wrap cmd f x) k z ↔
      ∃ w, Trace (SM.advance (Prog.compile (area cmd))) x k w ∧ z = wrap cmd f w := by
  constructor
  · intro hz
    obtain ⟨w, hw, _⟩ := trace_split h hk
    exact ⟨w, hw, trace_endpoint_unique hz (lift_run cmd route f hw)⟩
  · rintro ⟨w, hw, rfl⟩
    exact lift_run cmd route f hw

/-- At every time within a command the two machines have exactly the same
stack-height bound, including for the compiler's return stack. -/
theorem prefix_height_iff (f : F) {x y : Base cmd} {t k H : ℕ}
    (h : Trace (SM.advance (Prog.compile (area cmd))) x t y) (hk : k ≤ t)
    (j : Prog.Ix (area cmd)) :
    (∀ z, Trace (SM.advance (rule cmd route)) (wrap cmd f x) k z → (z.stack j).length ≤ H) ↔
      ∀ w, Trace (SM.advance (Prog.compile (area cmd))) x k w → (w.stack j).length ≤ H := by
  constructor
  · intro hw w run
    exact hw (wrap cmd f w) (lift_run cmd route f run)
  · intro hw z hz
    obtain ⟨w, run, rfl⟩ := (prefix_iff cmd route f h hk z).1 hz
    exact hw w run

/-- Compiled execution is valid even with parked letters on any data register
and a parked stack of return addresses. -/
theorem compile_phase (f : F) {r s : Reg Ltr} {t : ℕ}
    (h : Prog.Run [] (cmd f) r t s) (returns : List (Prog.Ptr (area cmd))) :
    Trace (SM.advance (Prog.compile (area cmd)))
      (Prog.machine (area cmd) (entry cmd f) r returns) t
      (Prog.machine (area cmd) none s returns) := by
  classical
  have hc := Prog.Run.compile_ok (area cmd) h (good cmd f) (fun i => by simp) returns
  convert hc using 2
  change some _ = if h : ([], cmd f) ∈ area cmd then some _ else none
  rw [dite_eq_left (good cmd f (Prog.sites_self _ _))]

theorem run_phase (f : F) {r s : Reg Ltr} {t : ℕ} (h : Prog.Run [] (cmd f) r t s) :
    Trace (SM.advance (rule cmd route)) (beginPhase cmd f r) t (endPhase cmd f s) :=
  lift_run cmd route f (compile_phase cmd f h [])

@[simp] theorem tops_output (f : F) (r : Reg Ltr) :
    SM.tops (endPhase cmd f r) (output cmd) = (r 0).head?.map Sum.inl := by
  simp [SM.tops, endPhase, wrap, Prog.machine, output]

private theorem branch {f : F} {r : Reg Ltr} (result : Option (F × Bool))
    (h : route f (SM.tops (endPhase cmd f r)) = result) :
    SM.advance (rule cmd route) (endPhase cmd f r) = result.map (fun (g, pop) =>
      SM.perform (endPhase cmd f r)
        ((g, entry cmd g), if pop then Function.update (fun _ => .skip) (output cmd) .pop
                       else fun _ => .skip)) := by
  classical
  change ((route f (SM.tops (endPhase cmd f r))).map _).map _ = _
  rw [h]
  cases result with
  | none => rfl
  | some pair => cases pair; rfl

theorem dispatch_skip {f g : F} {r : Reg Ltr}
    (h : route f (SM.tops (endPhase cmd f r)) = some (g, false)) :
    Trace (SM.advance (rule cmd route)) (endPhase cmd f r) 1 (beginPhase cmd g r) :=
  Trace.single (branch cmd route _ h)

theorem dispatch_pop {f g : F} {r : Reg Ltr}
    (h : route f (SM.tops (endPhase cmd f r)) = some (g, true)) :
    Trace (SM.advance (rule cmd route)) (endPhase cmd f r) 1
      (beginPhase cmd g (Function.update r 0 (r 0).tail)) := by
  classical
  apply Trace.single
  rw [branch cmd route _ h]
  change some (SM.Config.mk _ _) = some (SM.Config.mk _ _)
  rw [Option.some.injEq, SM.Config.mk.injEq]
  refine ⟨rfl, funext fun i => ?_⟩
  cases i with
  | none => rfl
  | some j =>
    by_cases hj : j.val = 0
    · have hzero : j = ⟨0, by simp [Prog.used]⟩ := Subtype.ext hj
      subst j
      simp [output, SM.Action.perform, endPhase, wrap, Prog.machine]
    · have he : some j ≠ output cmd := fun e => hj (congrArg Subtype.val (Option.some.inj e))
      simp [Function.update_of_ne he, Function.update_of_ne hj, SM.Action.perform, endPhase,
        wrap, Prog.machine]

theorem halt_phase {f : F} {r : Reg Ltr}
    (h : route f (SM.tops (endPhase cmd f r)) = none) :
    SM.advance (rule cmd route) (endPhase cmd f r) = none :=
  branch cmd route _ h

open Schoolbook (raw)

/-- Consume a leading flag on a raw record, keeping the rest of register zero intact. -/
theorem dispatch_pop_raw {f g : F} (a : Ltr) (s : List Ltr)
    (h : route f (SM.tops (endPhase cmd f (raw (a::s)))) = some (g, true)) :
    Trace (SM.advance (rule cmd route)) (endPhase cmd f (raw (a::s))) 1
      (beginPhase cmd g (raw s)) := by
  have he : Function.update (raw (a::s)) 0 ((raw (a::s)) 0).tail = raw s := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp [raw]
    · simp [raw, hi]
  simpa only [he] using dispatch_pop cmd route h

theorem begin_origin (f : F) (s : List Ltr) :
    beginPhase cmd f (raw s) = SM.origin (start cmd f) (output cmd) (s.map Sum.inl) := by
  classical
  change SM.Config.mk _ _ = SM.Config.mk _ _
  rw [SM.Config.mk.injEq]
  refine ⟨rfl, funext fun i => ?_⟩
  cases i with
  | none => rfl
  | some j =>
    change ((raw s) j.val).map Sum.inl = if some j = output cmd then _ else []
    by_cases h : j.val = 0
    · have eq : some j = output cmd := congrArg some (Subtype.ext h)
      simp [h, eq]
    · have ne : some j ≠ output cmd := fun e => h (congrArg Subtype.val (Option.some.inj e))
      simp [raw, h, ne]

theorem end_output (f : F) (r : Reg Ltr) :
    (endPhase cmd f r).stack (output cmd) = (r 0).map Sum.inl := rfl

theorem begin_height (f : F) (r : Reg Ltr) (H : ℕ) (hr : ∀ i, (r i).length ≤ H)
    (i : Prog.Ix (area cmd)) : ((beginPhase cmd f r).stack i).length ≤ H := by
  cases i with
  | none => exact Nat.zero_le _
  | some j => simpa [beginPhase, wrap, Prog.machine] using hr j.val

theorem end_height (f : F) (r : Reg Ltr) (H : ℕ) (hr : ∀ i, (r i).length ≤ H)
    (i : Prog.Ix (area cmd)) : ((endPhase cmd f r).stack i).length ≤ H := begin_height cmd f r H hr i

end ChunkDispatch

end NearSquareRoot
end Computability
end OAI
