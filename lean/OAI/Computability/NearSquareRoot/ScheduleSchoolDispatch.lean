import OAI.Computability.NearSquareRoot.ScheduleSchoolIO

/-!
# Repeated invocation of compiled schoolbook passes

Three fixed commands share the compiler's tapes and return stack. At the end of
the initialization and each digit pass, two stack transitions inspect the list
in the first field of the encoded state. They restore its enclosing pair marker
before starting the next command.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication IntegerMultiplication.Code

namespace Schoolbook.Dispatch

structure Programs where
  load : Cmd
  step : Cmd
  emit : Cmd

namespace Programs

noncomputable def area (p : Programs) : List (Prog.Loc Ltr) :=
  Prog.sites [] p.load ++ Prog.sites [] p.step ++ Prog.sites [] p.emit

variable (p : Programs)

instance : Finite (Prog.Ptr p.area) := by
  classical
  exact (Fintype.subtype p.area.toFinset (by simp)).finite

instance : Finite (Prog.Idx p.area) := by
  classical
  exact (Fintype.subtype (Prog.used p.area).toFinset (by simp)).finite

def output : Prog.Ix p.area := some ⟨0, by simp [Prog.used]⟩

private theorem good_load : Prog.Good p.area [] p.load := by
  intro l hl
  simp [area, hl]

private theorem good_step : Prog.Good p.area [] p.step := by
  intro l hl
  simp [area, hl]

private theorem good_emit : Prog.Good p.area [] p.emit := by
  intro l hl
  simp [area, hl]

private def entry (c : Cmd) (h : Prog.Good p.area [] c) : Prog.Pc p.area :=
  some ⟨([], c), h (Prog.sites_self _ _)⟩

abbrev Control := Option (Bool × Prog.Pc p.area)
abbrev Config := SM.Config (Prog.Sym p.area) p.Control (Prog.Ix p.area)

private def wrap (last : Bool) (x : SM.Config (Prog.Sym p.area) (Prog.Pc p.area) (Prog.Ix p.area)) :
    p.Config := ⟨some (last, x.pc), x.stack⟩

/-- Dispatch control `none` reads the remaining list after the opening pair
marker was popped. In `some (last,q)` the underlying compiler runs at `q`. -/
noncomputable def rule : SM.Rule (Prog.Sym p.area) p.Control (Prog.Ix p.area) := by
  classical
  exact fun pc stk => match pc with
    | some (last, q) =>
      match Prog.compile p.area q stk with
      | some (q', acts) => some (some (last, q'), acts)
      | none => if last then none else
          some (none, Function.update (fun _ => .skip) p.output .pop)
    | none =>
      let acts := Function.update (fun (_ : Prog.Ix p.area) => SM.Action.skip)
        p.output (.push (Sum.inl Ltr.node))
      match stk p.output with
      | some (.inl .node) => some (some (false, entry p p.step (good_step p)), acts)
      | some (.inl (.bit false)) => some (some (true, entry p p.emit (good_emit p)), acts)
      | _ => none

noncomputable def initial (r : Reg Ltr) : p.Config :=
  wrap p false (Prog.machine p.area (entry p p.load (good_load p)) r [])

noncomputable def ready (r : Reg Ltr) : p.Config :=
  wrap p false (Prog.machine p.area none r [])

noncomputable def done (r : Reg Ltr) : p.Config :=
  wrap p true (Prog.machine p.area none r [])

private theorem lift_one (last : Bool) {x y} (h : SM.advance (Prog.compile p.area) x = some y) :
    SM.advance p.rule (wrap p last x) = some (wrap p last y) := by
  classical
  cases hc : Prog.compile p.area x.pc (SM.tops x) with
  | none => simp [SM.advance, hc] at h
  | some qt =>
    obtain ⟨q, acts⟩ := qt
    simp only [SM.advance, hc, Option.map_some, Option.some.injEq] at h
    subst y
    change (match Prog.compile p.area x.pc (SM.tops x) with
      | some (q', acts) => some (some (last, q'), acts)
      | none => _).map _ = _
    rw [hc]
    rfl

private theorem lift_run (last : Bool) {x y t} (h : Trace (SM.advance (Prog.compile p.area)) x t y) :
    Trace (SM.advance p.rule) (wrap p last x) t (wrap p last y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (lift_one p last h) ih

private theorem compiled (c : Cmd) (hg : Prog.Good p.area [] c) (last : Bool)
    {r s t} (h : Prog.Run [] c r t s) :
    Trace (SM.advance p.rule) (wrap p last (Prog.machine p.area (entry p c hg) r [])) t
      (wrap p last (Prog.machine p.area none s [])) := by
  classical
  apply lift_run
  have hc := Prog.Run.compile_ok p.area h hg (fun i => by simp) []
  convert hc using 2
  change some _ = if h : ([],c) ∈ p.area then some _ else none
  rw [dite_eq_left (hg (Prog.sites_self _ _))]

theorem run_load {r s t} (h : Prog.Run [] p.load r t s) :
    Trace (SM.advance p.rule) (p.initial r) t (p.ready s) :=
  compiled p _ _ false h

private noncomputable def opened (r : Reg Ltr) : p.Config := by
  classical
  exact ⟨none, Function.update (p.ready r).stack p.output ((p.ready r).stack p.output).tail⟩

private theorem open_step (r : Reg Ltr) :
    SM.advance p.rule (p.ready r) = some (opened p r) := by
  classical
  change some (SM.perform _ (_, _)) = some _
  congr 1
  change SM.Config.mk _ _ = SM.Config.mk _ _
  rw [SM.Config.mk.injEq]
  refine ⟨rfl, ?_⟩
  funext i
  by_cases hi : i = p.output
  · subst i
    simp [SM.Action.perform]
  · simp [SM.Action.perform, Function.update_of_ne hi]

private theorem restore (r : Reg Ltr) (marker : (r 0).head? = some Ltr.node) :
    (SM.perform (opened p r)
      (some (true, none), Function.update (fun (_ : Prog.Ix p.area) => SM.Action.skip)
        p.output (.push (Sum.inl Ltr.node)))).stack = (p.ready r).stack := by
  classical
  funext i
  by_cases hi : i = p.output
  · subst i
    simp only [SM.perform, Function.update_self, SM.Action.perform, opened, ready, wrap,
      Prog.machine, output]
    cases h : r 0 with
    | nil => simp [h] at marker
    | cons a s => simpa [h] using marker.symm
  · simp [SM.perform, Function.update_of_ne hi, SM.Action.perform, opened]

private theorem top_open (r : Reg Ltr) :
    SM.tops (opened p r) p.output = ((r 0)[1]?).map Sum.inl := by
  classical
  simp only [SM.tops, opened, Function.update_self, ready, wrap, Prog.machine, output]
  cases h : r 0 with
  | nil => rfl
  | cons a s => cases s <;> rfl

private theorem select {r : Reg Ltr} (last : Bool) (c : Cmd) (hg : Prog.Good p.area [] c)
    (marker : (r 0).head? = some Ltr.node)
    (choice : (r 0)[1]? = some (if last then Ltr.bit false else .node))
    (hc : c = if last then p.emit else p.step) :
    Trace (SM.advance p.rule) (p.ready r) 2
      (wrap p last (Prog.machine p.area (entry p c hg) r [])) := by
  classical
  refine Trace.cons (open_step p r) (Trace.single ?_)
  have e := restore p r marker
  have hh := top_open p r
  rw [choice] at hh
  cases last <;> subst c
  all_goals
    change (match SM.tops (opened p r) p.output with
      | some (.inl .node) => some _
      | some (.inl (.bit false)) => some _
      | _ => none).map _ = _
    rw [hh]
    change some (SM.Config.mk _ _) = some (SM.Config.mk _ _)
    rw [Option.some.injEq, SM.Config.mk.injEq]
    exact ⟨rfl,e⟩

theorem run_step {r s t} (marker : (r 0).head? = some Ltr.node) (tag : (r 0)[1]? = some .node)
    (h : Prog.Run [] p.step r t s) :
    Trace (SM.advance p.rule) (p.ready r) (2+t) (p.ready s) :=
  (select p false p.step (good_step p) marker tag rfl).trans (compiled p _ (good_step p) false h)

theorem run_emit {r s t} (marker : (r 0).head? = some Ltr.node) (tag : (r 0)[1]? = some (.bit false))
    (h : Prog.Run [] p.emit r t s) :
    Trace (SM.advance p.rule) (p.ready r) (2+t) (p.done s) :=
  (select p true p.emit (good_emit p) marker tag rfl).trans (compiled p _ (good_emit p) true h)

theorem halt (r : Reg Ltr) : SM.advance p.rule (p.done r) = none := rfl

noncomputable def start : p.Control := (p.initial (raw [])).pc

theorem initial_origin (s : List Ltr) :
    p.initial (raw s) = SM.origin p.start p.output (s.map Sum.inl) := by
  classical
  change SM.Config.mk _ _ = SM.Config.mk _ _
  rw [SM.Config.mk.injEq]
  refine ⟨rfl, funext fun i => ?_⟩
  cases i with
  | none => rfl
  | some j =>
    change ((raw s) j.val).map Sum.inl = if some j = p.output then _ else []
    by_cases h : j.val = 0
    · have eq : some j = p.output := congrArg some (Subtype.ext h)
      simp [h, eq]
    · have ne : some j ≠ p.output := fun e => h (congrArg Subtype.val (Option.some.inj e))
      simp [raw, h, ne]

theorem done_output (s : List Ltr) : (p.done (raw s)).stack p.output = s.map Sum.inl := rfl

theorem initial_height (s : List Ltr) (i : Prog.Ix p.area) :
    ((p.initial (raw s)).stack i).length ≤ s.length := by
  classical
  rw [initial_origin]
  simp only [SM.origin]
  split <;> simp

theorem ready_height (s : List Ltr) (i : Prog.Ix p.area) :
    ((p.ready (raw s)).stack i).length ≤ s.length := p.initial_height s i

theorem done_height (s : List Ltr) (i : Prog.Ix p.area) :
    ((p.done (raw s)).stack i).length ≤ s.length := p.initial_height s i

end Programs
end Schoolbook.Dispatch

end NearSquareRoot
end Computability
end OAI
