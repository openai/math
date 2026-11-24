import OAI.Computability.VPVNP.LiveHeaderProgramRun

/-!
# Composable native header prefixes

Each prefix starts and ends at a particular stage and memory. This makes
the transfer write and cursor reset part of the interface between successive
blocks, including at the boundary between the index and advice scans.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule
variable {w : ℕ}

/-- A full component run in the actual row, with enough budget for the
uniform outer instruction cap. -/
def StageTrace.Good (x : StageTrace w) (s : Sizes) : Prop :=
  x.fuel ≤ 40 ∧ x.paths = List.replicate (calls s (stage x.id)) [] ∧
  x.reports.length = calls s (stage x.id) ∧ ∀ r ∈ x.reports, r.probes ≤ probes (stage x.id)

/-- The source stage runs from the given cursor zero and accepts. -/
structure StageTrace.Exec (x : StageTrace w) (s : Sizes) (base : ℕ) (m : Memory w) : Prop where
  source : runSegment ((stageTemplate (stage x.id)).2.instantiate w (rowData w s base (stage x.id))).program
    x.fuel (some 0) m x.paths = some x.reports
  accept : endState (some 0) x.reports = none
  frame : LiveStageLink.PreservesTagOnReturns (Fin.ofNat _ base) m x.reports

/-- A consecutive sequence of executed header stages whose transferred memory and next stage
match the entry to each succeeding call. -/
inductive StagePrefix (s : Sizes) (base : ℕ) :
    Option StageId → Memory w → List (StageTrace w) → Option StageId → Memory w → Prop
  | nil (id : Option StageId) (m : Memory w) : StagePrefix s base id m [] id m
  | cons (x : StageTrace w) {m : Memory w} {xs : List (StageTrace w)} {dest : Option StageId} {final : Memory w}
      (localRun : x.Exec s base m)
      (rest : StagePrefix s base (next x.id) (x.finalMem (Fin.ofNat _ base) m) xs dest final) :
      StagePrefix s base (some x.id) m (x :: xs) dest final

theorem StagePrefix.single {s : Sizes} {base : ℕ} {m : Memory w} {x : StageTrace w}
    (hx : x.Exec s base m) :
    StagePrefix s base (some x.id) m [x] (next x.id) (x.finalMem (Fin.ofNat _ base) m) :=
  .cons x hx (.nil _ _)

theorem StagePrefix.append {s : Sizes} {base : ℕ} {i j k : Option StageId} {m n o : Memory w}
    {xs ys : List (StageTrace w)} (a : StagePrefix s base i m xs j n) (b : StagePrefix s base j n ys k o) :
    StagePrefix s base i m (xs++ys) k o := by
  induction a with
  | nil => exact b
  | cons x run _ ih => exact .cons x run (ih b)

theorem StagePrefix.finish {s : Sizes} {base : ℕ} {i j : Option StageId} {m n : Memory w}
    {xs ys : List (StageTrace w)} (a : StagePrefix s base i m xs j n) (b : StageRuns s base j n ys) :
    StageRuns s base i m (xs++ys) := by
  induction a with
  | nil => exact b
  | cons x run _ ih => exact .cons x run.source run.accept run.frame (ih b)

theorem StagePrefix.finalMemory {s : Sizes} {base : ℕ} {i j : Option StageId} {m n : Memory w}
    {xs : List (StageTrace w)} (a : StagePrefix s base i m xs j n) :
    LiveHeaderProgram.finalMemory (Fin.ofNat _ base) m xs = n := by
  induction a with
  | nil => rfl
  | cons _ _ _ ih => exact ih

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
