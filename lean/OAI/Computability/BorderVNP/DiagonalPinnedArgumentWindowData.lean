import OAI.Computability.BorderVNP.DiagonalJointSparseInputClock

/-! # A public schedule and the charge of every sparse source reached on it -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM BorderVNP.Cube Physical ScheduleClock DiagonalTallyCellReports CellDispatch

/-- The owner table is chosen at the end of the true public schedule. A
report may be submitted afterwards on that table; its chronological
argument trace and all private directory probes fit the same allowance. -/
structure PublishedArgumentWindow {teams n w : ℕ} {A : Type} [Fintype A]
    (a : SignedTaskArena.Layout) (id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ)
    (U : Fin (teams+1) → PinStart SparseExterior.driver n w) {u : Fin (teams+1)} (p : (U u).Prefix id)
    (decl : LengthDeclaration a.cube.n a.cube.header.d)
    (label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d) (recv : A → Fin a.cube.cells) (incoming : A → ℕ)
    (X description wp wd copies parameters expBits : ℕ) (fr : FragmentRows.Layout) (ctrl : CellControlRows.Layout)
    (emitted : ℕ → ℕ) (budget : ℕ) where
  /-- Grouping input read from the original public interval return. -/
  profile : ℕ → ℕ
  /-- Word image after the native greedy allocation. -/
  assigned : ℕ → ℕ
  /-- The owner table was written by the selected greedy program. -/
  scheduled : GroupWeights.ScheduleResult (LocalRow.weightLayout a.cube ((U u).pub 0).val decl.1.val)
    (LocalRow.teamLayout a.cube teams) profile assigned
  /-- Underlying network labels and delivered widths for those very weights. -/
  image : GroupWeights.PhysicalImage (LocalRow.weightLayout a.cube ((U u).pub 0).val decl.1.val)
    profile a.cube.header.blocks a.cube.b a.cube.K a.cube.h decl label recv incoming
  /-- The actual local and joint group guards on the elected word image. -/
  pass : (TeamBudget.Layout.mk (teams+1) X a.cube.teamTotals).Passes assigned
  /-- A source on the elected table determines a bound for the original
  native prefix, including probes in the issued private directory. -/
  charge : let pub := (U u).pub
    let V := visits id U p
    let input := afterRoute id U p
    ∀ (Site E I P : Type) [Fintype P] (native : SparseSource id U p)
      (S : SparseReportSources Site E I P a.cube decl label recv incoming assigned u.val description wp wd copies
        parameters expBits native.source fr (readings V.reports.val.2.2) ctrl emitted),
      ProducedRoster a ctrl emitted S.places S.geometry S.extra native.source →
      ∀ cursor : ReportCursor, PreparedReportInput pub V.controls.val.2.2 S.reportRows cursor description →
      traceCost input.val.1+privateDirectoryTicks pub input.val.2.2 ≤ budget

/-- Identify the native fragment and emitter memory once, before choosing
the existential report source. This preserves both chosen schedule images. -/
theorem PublishedArgumentWindow.of_emitted {teams n w : ℕ} {A : Type} [Fintype A] (a : SignedTaskArena.Layout)
    (id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ)
    (U : Fin (teams+1) → PinStart SparseExterior.driver n w) (u : Fin (teams+1)) (p : (U u).Prefix id)
    (decl : LengthDeclaration a.cube.n a.cube.header.d)
    (label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d) (recv : A → Fin a.cube.cells) (incoming : A → ℕ)
    (X description wp wd copies parameters expBits : ℕ) (ctrl : CellControlRows.Layout)
    (emitted current : ℕ → ℕ) (budget : ℕ) (same : emitted=current)
    (fr : FragmentDirectoryInput (U u).pub (visits id U p).reports.val.2.2)
    (profile assigned : ℕ → ℕ)
    (schedule : GroupWeights.ScheduleResult (LocalRow.weightLayout a.cube ((U u).pub 0).val decl.1.val)
      (LocalRow.teamLayout a.cube teams) profile assigned)
    (image : GroupWeights.PhysicalImage (LocalRow.weightLayout a.cube ((U u).pub 0).val decl.1.val)
      profile a.cube.header.blocks a.cube.b a.cube.K a.cube.h decl label recv incoming)
    (pass : (TeamBudget.Layout.mk (teams+1) X a.cube.teamTotals).Passes assigned)
    (charge : ∀ (Site E I P : Type) [Fintype P] (native : SparseSource id U p)
        (S : SparseReportSources Site E I P a.cube decl label recv incoming assigned u.val description wp wd copies
          parameters expBits native.source fr.layout (readings (visits id U p).reports.val.2.2) ctrl current),
        ProducedRoster a ctrl current S.places S.geometry S.extra native.source →
        ∀ cursor : ReportCursor, PreparedReportInput (U u).pub (visits id U p).controls.val.2.2 S.reportRows cursor description →
        traceCost (afterRoute id U p).val.1+privateDirectoryTicks (U u).pub (afterRoute id U p).val.2.2 ≤ budget) :
    ∃ window : PublishedArgumentWindow a id U (u:=u) p decl label recv incoming X description wp wd copies parameters expBits
      (FragmentRows.Layout.fromFrame ((U u).pub 0).val (readings (visits id U p).reports.val.2.2)) ctrl emitted budget,
      window.profile=profile ∧ window.assigned=assigned := by
  have found : ∃ window : PublishedArgumentWindow a id U (u:=u) p decl label recv incoming X description wp wd copies parameters
      expBits fr.layout ctrl current budget, window.profile=profile ∧ window.assigned=assigned :=
    ⟨⟨profile,assigned,schedule,image,pass,charge⟩,rfl,rfl⟩
  rw [fr.loaded,←same] at found
  exact found

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
