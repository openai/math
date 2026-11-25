import OAI.Computability.NearSquareRoot.ScheduleChunkControl

/-! # Interrupting the compiled chunk driver at a digit request

The fixed controller and its return stack run on their usual shared machine.
Entering the digit phase pauses the machine before its first instruction.
After a call, the same finite controller can start its collection phase on
the returned register assignment.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingOpen

open IntegerMultiplication IntegerMultiplication.Code Schoolbook
open ChunkControl (Driver Phase Height)
open ChunkDispatch (area beginPhase endPhase wrap)

variable (d : Driver)

/-- The unused digit instruction reserves register one in the common compiler
table. Digit execution itself is supplied by the external machine. -/
abbrev cmd := ChunkControl.program d (.pop 0)

/-- The shared stack register used to exchange digit operands and replies. -/
def one : Prog.Ix (area (cmd d)) := some ⟨1, by
  apply List.mem_cons_of_mem
  apply List.mem_map.mpr
  exact ⟨([], cmd d .digit), ChunkDispatch.good (cmd d) .digit (Prog.sites_self _ _), rfl⟩⟩

theorem one_ne_output : one d ≠ ChunkDispatch.output (cmd d) := by
  intro h
  have := congrArg Subtype.val (Option.some.inj h)
  exact Nat.one_ne_zero this

@[simp] theorem begin_one (f : Phase) (r : Reg Ltr) :
    (beginPhase (cmd d) f r).stack (one d) = (r 1).map Sum.inl := rfl

@[simp] theorem end_one (f : Phase) (r : Reg Ltr) :
    (endPhase (cmd d) f r).stack (one d) = (r 1).map Sum.inl := rfl

/-- Register one is initially empty, so its physical bottom is its initial
head position, zero. -/
theorem initial_bottom_one (s : List Ltr) (T : Prog.Ix (area (cmd d)) →
    TM.Tape (Option (Prog.Sym (area (cmd d))))) (h : (T (one d)).pos = 0) :
    (T (one d)).pos + (((beginPhase (cmd d) .load (raw s)).stack (one d)).length : ℤ) = 0 := by
  simp [h, raw]

noncomputable def rule :
    SM.Rule (Prog.Sym (area (cmd d))) (ChunkDispatch.Control (cmd d)) (Prog.Ix (area (cmd d))) :=
  fun pc seen => if pc.1 = .digit then none else ChunkControl.machine (cmd d) pc seen

@[simp] theorem pause (pc : Prog.Pc (area (cmd d))) (tops) :
    rule d (.digit,pc) tops = none := rfl

theorem advance_of_ne (x : ChunkDispatch.Config (cmd d)) (hf : x.pc.1 ≠ .digit) :
    SM.advance (rule d) x = SM.advance (ChunkControl.machine (cmd d)) x := by
  simp [SM.advance, rule, hf]

/-- Interrupting at digit requests leaves every compiled instruction in any
other phase available with its original step count. -/
theorem lift_run {f : Phase} (hf : f ≠ .digit) {x y : ChunkDispatch.Base (cmd d)} {t : ℕ}
    (h : Trace (SM.advance (Prog.compile (area (cmd d)))) x t y) :
    Trace (SM.advance (rule d)) (wrap (cmd d) f x) t (wrap (cmd d) f y) := by
  induction h with
  | nil => exact .nil _
  | cons step _ ih =>
    exact .cons ((advance_of_ne d _ hf).trans
      (ChunkDispatch.lift_one (cmd d) (ChunkControl.route (cmd d)) f step)) ih

/-- Compiled segments retain their exact time and their certified height,
even when the height bound is smaller than the command's running time. -/
theorem lift_segment {f : Phase} (hf : f ≠ .digit) {x y : ChunkDispatch.Base (cmd d)}
    {t H : ℕ} (h : Segment (Prog.compile (area (cmd d))) x t y H) :
    Segment (rule d) (wrap (cmd d) f x) t (wrap (cmd d) f y) H := by
  refine ⟨lift_run d hf h.run, fun {k z} hk cut j => ?_⟩
  obtain ⟨u, hu, _⟩ := trace_split h.run hk
  rw [trace_endpoint_unique cut (lift_run d hf hu)]
  exact h.height hk hu j

theorem phase_run {f : Phase} {r s : Reg Ltr} {t : ℕ} (hf : f ≠ .digit)
    (run : Prog.Run [] (cmd d f) r t s) :
    Trace (SM.advance (rule d)) (beginPhase (cmd d) f r) t (endPhase (cmd d) f s) :=
  lift_run d hf (ChunkDispatch.compile_phase (cmd d) f run [])

/-- In particular, no proper prefix of a compiled command can reach a digit
request. The endpoint still carries the same phase tag. -/
theorem phase_tag {f : Phase} {r s : Reg Ltr} {t k : ℕ} (hf : f ≠ .digit)
    (run : Prog.Run [] (cmd d f) r t s) (hk : k ≤ t) {z}
    (cut : Trace (SM.advance (rule d)) (beginPhase (cmd d) f r) k z) : z.pc.1 = f := by
  obtain ⟨x, hx, _⟩ := trace_split (ChunkDispatch.compile_phase (cmd d) f run []) hk
  have eq := trace_endpoint_unique cut (lift_run d hf hx)
  exact congrArg (fun c => c.pc.1) eq

theorem phase {f : Phase} {r s : Reg Ltr} {t R B H : ℕ} (hf : f ≠ .digit)
    (run : Prog.Run [] (cmd d f) r t s) (hr : Height r R) (ht : t ≤ B) (hh : R+B ≤ H) :
    Segment (rule d) (beginPhase (cmd d) f r) t (endPhase (cmd d) f s) H :=
  (Segment.of_cost (phase_run d hf run) (ChunkDispatch.begin_height (cmd d) f r R hr) ht).mono hh

theorem positive {A : Type} {Γ : Scope A} {c : Prog A} {r s : Reg A} {t : ℕ}
    (run : Prog.Run Γ c r t s) : 0 < t := by
  cases run <;> omega

private theorem single {x y : ChunkDispatch.Config (cmd d)} (hf : x.pc.1 ≠ .digit)
    (h : Trace (SM.advance (ChunkControl.machine (cmd d))) x 1 y) :
    Trace (SM.advance (rule d)) x 1 y := by
  generalize e : 1 = n at h
  cases h with
  | nil => omega
  | @cons _ u _ n hs tail =>
    have en : n = 0 := by omega
    subst n
    have eq := trace_endpoint_unique tail (.nil u)
    rw [eq]
    exact Trace.single ((advance_of_ne d _ hf).trans hs)

theorem skip {f g : Phase} {s : Reg Ltr} {R H : ℕ} (hf : f ≠ .digit)
    (branch : ChunkControl.route (cmd d) f (SM.tops (endPhase (cmd d) f s)) = some (g,false))
    (hr : Height s R) (hh : R+1 ≤ H) :
    Segment (rule d) (endPhase (cmd d) f s) 1 (beginPhase (cmd d) g s) H :=
  (Segment.of_cost
    (single d hf (ChunkDispatch.dispatch_skip (cmd d) (ChunkControl.route (cmd d)) branch))
    (ChunkDispatch.end_height (cmd d) f s R hr) le_rfl).mono hh

theorem test (s : List Ltr) (flag : Bool) {H : ℕ} (hh : s.length+2 ≤ H) :
    Segment (rule d) (endPhase (cmd d) .test (raw (.bit flag::s))) 1
      (beginPhase (cmd d) (if flag then .emit else .prepare) (raw s)) H := by
  have branch : ChunkControl.route (cmd d) .test
      (SM.tops (endPhase (cmd d) .test (raw (.bit flag::s)))) =
      some (if flag then .emit else .prepare, true) := by
    rw [ChunkControl.route, ChunkDispatch.tops_output]
    rfl
  have step := ChunkDispatch.dispatch_pop_raw (cmd d) (ChunkControl.route (cmd d))
    (.bit flag) s branch
  exact (Segment.of_cost (single d (show Phase.test ≠ .digit by decide) step)
    (ChunkDispatch.end_height (cmd d) _ _ (s.length+1) (ChunkControl.raw_height _ le_rfl))
    le_rfl).mono hh

theorem halt (r : Reg Ltr) : SM.advance (rule d) (endPhase (cmd d) .emit r) = none :=
  (advance_of_ne d _ (show Phase.emit ≠ .digit by decide)).trans (ChunkControl.halt_output r)

end StagingOpen

end NearSquareRoot
end Computability
end OAI
