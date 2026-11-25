import OAI.Computability.NearSquareRoot.ShortWordSpace

/-! # Repeated handoff between the controller and the physical digit routine

The two finite transition tables share one bank of tapes. A paused controller
starts the digit routine. A returning digit routine resumes the controller at
a fixed instruction. Each handoff is one stationary physical transition.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingCycle

open IntegerMultiplication TM

variable {A C D I : Type}

/-- The calling convention is fixed independently of the digit index. -/
structure Driver (A C D I : Type) where
  controller : Rule A C I
  digit : Rule A D I
  paused : C → Bool
  start : D
  resume : C

def controller (x : Config A C I) : Config A (C ⊕ D) I := ⟨.inl x.pc,x.tape⟩
def digit (x : Config A D I) : Config A (C ⊕ D) I := ⟨.inr x.pc,x.tape⟩

namespace Driver

variable (g : Driver A C D I)

def rule : Rule A (C ⊕ D) I
  | .inl q, h => match g.controller q h with
    | some (q',op) => some (.inl q',op)
    | none => if g.paused q then some (.inr g.start,fun i => (h i,.stay)) else none
  | .inr q, h => match g.digit q h with
    | some (q',op) => some (.inr q',op)
    | none => some (.inl g.resume,fun i => (h i,.stay))

theorem controller_step {x y} (h : advance g.controller x = some y) :
    advance g.rule (StagingCycle.controller x) = some (StagingCycle.controller y) := by
  cases e : g.controller x.pc (fun i => (x.tape i).view 0) with
  | none => simp [advance,e] at h
  | some pair =>
    obtain ⟨q,ops⟩ := pair
    simp only [advance,e,Option.map_some,Option.some.injEq] at h
    subst y
    simp [advance,rule,StagingCycle.controller,e]

theorem digit_step {x y} (h : advance g.digit x = some y) :
    advance g.rule (StagingCycle.digit x) = some (StagingCycle.digit y) := by
  cases e : g.digit x.pc (fun i => (x.tape i).view 0) with
  | none => simp [advance,e] at h
  | some pair =>
    obtain ⟨q,ops⟩ := pair
    simp only [advance,e,Option.map_some,Option.some.injEq] at h
    subst y
    simp [advance,rule,StagingCycle.digit,e]

theorem controller_trace {x y t} (h : Trace (advance g.controller) x t y) :
    Trace (advance g.rule) (StagingCycle.controller x) t (StagingCycle.controller y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (g.controller_step hs) ih

theorem digit_trace {x y t} (h : Trace (advance g.digit) x t y) :
    Trace (advance g.rule) (StagingCycle.digit x) t (StagingCycle.digit y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (g.digit_step hs) ih

/-- A paused controller starts the digit routine on exactly its current tapes. -/
theorem enter (x : Config A C I) (stop : advance g.controller x = none) (paused : g.paused x.pc = true) :
    advance g.rule (StagingCycle.controller x) = some (StagingCycle.digit ⟨g.start,x.tape⟩) := by
  have e : g.controller x.pc (fun i => (x.tape i).view 0) = none := by simpa [advance] using stop
  simp [advance,rule,StagingCycle.controller,StagingCycle.digit,e,paused,SM.Action.apply_stay]

/-- A completed digit routine resumes the collect phase with its actual tape contents. -/
theorem leave (x : Config A D I) (stop : advance g.digit x = none) :
    advance g.rule (StagingCycle.digit x) = some (StagingCycle.controller ⟨g.resume,x.tape⟩) := by
  have e : g.digit x.pc (fun i => (x.tape i).view 0) = none := by simpa [advance] using stop
  simp [advance,rule,StagingCycle.controller,StagingCycle.digit,e,SM.Action.apply_stay]

theorem halt (x : Config A C I) (stop : advance g.controller x = none) (finished : g.paused x.pc = false) :
    advance g.rule (StagingCycle.controller x) = none := by
  have e : g.controller x.pc (fun i => (x.tape i).view 0) = none := by simpa [advance] using stop
  simp [advance,rule,StagingCycle.controller,e,finished]

theorem controller_prefix {x y t} (run : Trace (advance g.controller) x t y) {k z} (hk : k ≤ t)
    (cut : Trace (advance g.rule) (StagingCycle.controller x) k z) :
    ∃ c, Trace (advance g.controller) x k c ∧ z = StagingCycle.controller c := by
  obtain ⟨c,h,_⟩ := trace_split run hk
  exact ⟨c,h,trace_endpoint_unique cut (g.controller_trace h)⟩

theorem digit_prefix {x y t} (run : Trace (advance g.digit) x t y) {k z} (hk : k ≤ t)
    (cut : Trace (advance g.rule) (StagingCycle.digit x) k z) :
    ∃ c, Trace (advance g.digit) x k c ∧ z = StagingCycle.digit c := by
  obtain ⟨c,h,_⟩ := trace_split run hk
  exact ⟨c,h,trace_endpoint_unique cut (g.digit_trace h)⟩

theorem controller_fenced {lo hi x y t} (run : FencedRun g.controller lo hi x t y) :
    FencedRun g.rule lo hi (StagingCycle.controller x) t (StagingCycle.controller y) := by
  refine ⟨g.controller_trace run.1,fun k hk z cut => ?_⟩
  obtain ⟨c,h,rfl⟩ := g.controller_prefix run.1 hk cut
  exact run.2 k hk c h

theorem digit_fenced {lo hi x y t} (run : FencedRun g.digit lo hi x t y) :
    FencedRun g.rule lo hi (StagingCycle.digit x) t (StagingCycle.digit y) := by
  refine ⟨g.digit_trace run.1,fun k hk z cut => ?_⟩
  obtain ⟨c,h,rfl⟩ := g.digit_prefix run.1 hk cut
  exact run.2 k hk c h

private theorem stationary_fenced {lo hi : I → ℤ} {x y : Config A (C ⊕ D) I}
    (h : advance g.rule x = some y) (eq : x.tape = y.tape)
    (hx : ∀ i, lo i ≤ (x.tape i).pos ∧ (x.tape i).pos ≤ hi i) :
    FencedRun g.rule lo hi x 1 y := by
  refine ⟨.single h,fun k hk z cut => ?_⟩
  have ht : k = 0 ∨ k = 1 := by omega
  rcases ht with rfl | rfl
  · have he := trace_endpoint_unique cut (.nil x)
    simpa only [he] using hx
  · have he := trace_endpoint_unique cut (.single h)
    simpa only [he,← eq] using hx

theorem enter_fenced {lo hi} (x : Config A C I) (stop : advance g.controller x = none)
    (paused : g.paused x.pc = true) (hx : ∀ i, lo i ≤ (x.tape i).pos ∧ (x.tape i).pos ≤ hi i) :
    FencedRun g.rule lo hi (StagingCycle.controller x) 1 (StagingCycle.digit ⟨g.start,x.tape⟩) :=
  g.stationary_fenced (g.enter x stop paused) rfl hx

theorem leave_fenced {lo hi} (x : Config A D I) (stop : advance g.digit x = none)
    (hx : ∀ i, lo i ≤ (x.tape i).pos ∧ (x.tape i).pos ≤ hi i) :
    FencedRun g.rule lo hi (StagingCycle.digit x) 1 (StagingCycle.controller ⟨g.resume,x.tape⟩) :=
  g.stationary_fenced (g.leave x stop) rfl hx

/-- A complete external call, including both stationary changes of control. -/
theorem call_fenced {lo hi} (x : Config A C I) {y : Config A D I} {t}
    (stop : advance g.controller x = none) (paused : g.paused x.pc = true)
    (run : FencedRun g.digit lo hi ⟨g.start,x.tape⟩ t y) (back : advance g.digit y = none) :
    FencedRun g.rule lo hi (StagingCycle.controller x) (1+t+1)
      (StagingCycle.controller ⟨g.resume,y.tape⟩) :=
  ((g.enter_fenced x stop paused (run.2 0 (Nat.zero_le _) _ (.nil _))).trans
    (g.digit_fenced run)).trans (g.leave_fenced y back (run.2 t le_rfl y run.1))

/-- Run all rows and finish on the original controller's halted configuration.
Each row pays both dispatches and reuses the same absolute tape intervals. -/
theorem run_fenced {lo hi : I → ℤ} {initial final : Config A C I}
    (row ready : ℕ → Config A C I) (reply : ℕ → Config A D I) (n : ℕ)
    {L O T R E : ℕ}
    (launch : ∃ t ≤ L, FencedRun g.controller lo hi initial t (row 0))
    (offer : ∀ i < n, ∃ t ≤ O, FencedRun g.controller lo hi (row i) t (ready i))
    (request : ∀ i < n, advance g.controller (ready i) = none ∧ g.paused (ready i).pc = true)
    (call : ∀ i < n, ∃ t ≤ T, FencedRun g.digit lo hi ⟨g.start,(ready i).tape⟩ t (reply i) ∧
      advance g.digit (reply i) = none)
    (recover : ∀ i < n, ∃ t ≤ R, FencedRun g.controller lo hi ⟨g.resume,(reply i).tape⟩ t (row (i+1)))
    (complete : ∃ t ≤ E, FencedRun g.controller lo hi (row n) t final)
    (halted : advance g.controller final = none) (finished : g.paused final.pc = false) :
    ∃ t ≤ L+n*(O+T+R+2)+E,
      FencedRun g.rule lo hi (StagingCycle.controller initial) t (StagingCycle.controller final) ∧
      advance g.rule (StagingCycle.controller final) = none := by
  have rows (j : ℕ) (hj : j ≤ n) : ∃ t ≤ L+j*(O+T+R+2),
      FencedRun g.rule lo hi (StagingCycle.controller initial) t (StagingCycle.controller (row j)) := by
    induction j with
    | zero =>
      obtain ⟨t,ht,run⟩ := launch
      exact ⟨t,by simpa using ht,g.controller_fenced run⟩
    | succ i ih =>
      have hi : i < n := by omega
      obtain ⟨s,hs,previous⟩ := ih hi.le
      obtain ⟨a,ha,send⟩ := offer i hi
      obtain ⟨b,hb,digitRun,back⟩ := call i hi
      obtain ⟨c,hc,resume⟩ := recover i hi
      obtain ⟨stop,paused⟩ := request i hi
      have digitCall := g.call_fenced _ stop paused digitRun back
      exact ⟨_,by rw [Nat.succ_mul]; omega,
        (((previous.trans (g.controller_fenced send)).trans digitCall).trans (g.controller_fenced resume))⟩
  obtain ⟨s,hs,work⟩ := rows n le_rfl
  obtain ⟨t,ht,last⟩ := complete
  exact ⟨s+t,Nat.add_le_add hs ht,work.trans (g.controller_fenced last),g.halt final halted finished⟩

end Driver
end StagingCycle

end NearSquareRoot
end Computability
end OAI
