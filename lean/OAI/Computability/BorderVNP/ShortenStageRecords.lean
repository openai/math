import OAI.Computability.BorderVNP.ShortenCatalogCertificates
import OAI.Computability.BorderVNP.ShortenRetainedLoadStep

/-!
# Keeping both physical record bounds on the selected stage path

The record bound quantifies over all prior records and private payloads
on the actual child sites and over both counting modes. One joint choice
of motion and placement supplies the analytic measurements, successor
catalog membership and physical record update for every histogram.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Cover Epoch Crossing Adaptive
open scoped Classical

variable {D m k b d d' : ℕ} [NeZero D] {K : Type*} [Field K] {I P B : Type} [Fintype I]
    [Fintype B] {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d}

/-- A uniform bound on descriptor count and expanded weight at every
output tile, for arbitrary input site data on this exact chosen step. -/
def PlacedStep.RecordFactor (s : PlacedStep m B d' child) (e : PaidIdentity K D m) (C : ℕ) : Prop :=
  ∀ [Fintype P] (q : s.Index e) (ex : Bool) (prior payload : ∀ i, (child i).pack.layout.Site → ℕ) (M : ℕ),
    (∀ i t, localRecords (child i).pack.layout ex (prior i) (payload i)
      (fun v => productTileName d ((child i).site v) = t) ≤ M) →
    ∀ o, 1 + s.resultLocalRecords e q ex prior payload o ≤ C*k*(1+M)

namespace Adaptive

variable {e : PaidIdentity K D m} {hCap hSaving ν : ℝ} {S : Finset (HyperbolicHost I)}

/-- A stage's jointly realizable record factor. All future table entries,
fan-ins, quotient levels, and histograms use the same C. -/
def StageTemplate.HasRecordFactor (t : StageTemplate e I hCap hSaving ν S) (C : ℕ) : Prop :=
  ∀ (d : ℕ), t.floor ≤ d → ∀ {k : ℕ} (hk : 0 < k) {P : Type} {bits : P → ℕ}
    (child : Fin k → PlacedPack D P bits K I (d+2*t.word)), (∀ i, Catalog.PlacedAt S hCap (child i)) →
    ∃ s : PlacedStep m t.Bin d child,
      Nonempty (PlacedStep.Measurements s hk hSaving ν t.meanFactor t.motionFactor) ∧
        s.RecordFactor e C ∧ ∀ q : s.Index e, Catalog.PlacedAt t.nextSites hCap (s.result e q)

/-- Transport the joint record and motion certificate along a scheduled level equality. -/
theorem StageTemplate.HasRecordFactor.atLevel {t : StageTemplate e I hCap hSaving ν S} {C : ℕ}
    (cert : t.HasRecordFactor C) {old next : ℕ} (heq : old = next+2*t.word) (hf : t.floor ≤ next)
    (hk : 0 < k) (child : Fin k → PlacedPack D P bits K I old) (valid : ∀ i, Catalog.PlacedAt S hCap (child i)) :
    ∃ s : PlacedStep m t.Bin next child,
      Nonempty (PlacedStep.Measurements s hk hSaving ν t.meanFactor t.motionFactor) ∧
        s.RecordFactor e C ∧ ∀ q : s.Index e, Catalog.PlacedAt t.nextSites hCap (s.result e q) := by
  subst old
  exact cert next hf hk child valid

/-- One actual program carries both its measurements and a uniform record
factor for each selected step. All stored sites, wires and payload slots
are the physical output of that same selected histogram. -/
theorem StagePath.program_at_start_records (path : StagePath b e I hCap hSaving ν)
    (C : Fin b → ℕ) (hc : ∀ i, (path.pattern i).HasRecordFactor (C i))
    (last lastFloor high : ℕ) (hh : path.threshold last lastFloor ≤ high) (hk : 0 < k) :
    ∃ F : Program (B := fun i => (path.pattern i).Bin) e (fun j (p : path.State P bits k last high j) => p.val),
      (∀ i c, Nonempty (PlacedStep.Measurements (F.step i c) hk hSaving ν
        (path.pattern i).meanFactor (path.pattern i).motionFactor)) ∧
      (∀ i c, (F.step i c).RecordFactor e (C i)) ∧
      ∀ i c q, (F.advance i c q).val = (F.step i c).result e q := by
  let word := fun i => (path.pattern i).word
  let terminal := high - Levels.totalDrop word last
  obtain ⟨_,_,floor⟩ := Levels.of_start word last lastFloor (fun i => (path.pattern i).floor) hh
  apply path.exists_program_with last high hk (fun i _ s => s.RecordFactor e (C i))
  intro i c
  obtain ⟨s,meas,records,closed⟩ := (hc i).atLevel (Levels.step_depth word terminal last i)
    (floor i) hk (fun j => (c j).val) (fun j => (c j).property)
  exact ⟨s,meas,records,fun q => path.next i ▸ closed q⟩

end Adaptive
end Shortening

end BorderVNP
end Computability
end OAI
