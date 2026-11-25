import OAI.Computability.BorderVNP.ShortenStageSchedule
import OAI.Computability.BorderVNP.ShortenPhysicalClosed
import OAI.Computability.BorderVNP.ShortenPreparedChildren

/-!
# From finitely prepared stage templates to the concrete physical program

The stage's relative sites, length cutoff, word length, quotient depth
threshold and concentration constants are fixed before its fan-in or input
packs. Its operation acts on the actual child networks. The canonical
histogram outputs are stored directly, including their tracked midpoints.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Cover Crossing Epoch CombiningStep PlacedStep
open scoped Classical

variable {D m k d : ℕ} {I P : Type} [Fintype I] {K : Type*} {bits : P → ℕ}

/-- The three geometric properties needed as inputs to the prepared
motion, signed-bin matching and concentration selection. -/
structure Catalog.PlacedAt (S : Finset (HyperbolicHost I)) (h : ℝ)
    (p : PlacedPack D P bits K I d) : Prop where
  /-- Every retained or inserted vertex is in a listed relative site class. -/
  sites : ∀ v, Catalog.relative d (p.site v) ∈ S
  /-- All charged cables satisfy the same fixed short scale. -/
  short : ∀ c, p.charged c = true → dist (p.site (p.pack.layout.src c)) (p.site (p.pack.layout.dst c)) ≤ 2*h
  /-- The tracked center of every active cable lies within half its endpoint distance of its source. -/
  midpoint : ∀ c, p.active c = true → dist (p.midpoint c) (p.site (p.pack.layout.src c)) ≤
    dist (p.site (p.pack.layout.src c)) (p.site (p.pack.layout.dst c)) / 2

variable [NeZero D] [Field K] {B : Type} [Fintype B] {child : Fin k → PlacedPack D P bits K I d} {out : ℕ}

/-- The successor catalog and unchanged short cap establish the full
preparation predicate on each actual output. Its tracked midpoint is
the quotient midpoint of these very endpoints. -/
theorem Catalog.PlacedAt.result (e : PaidIdentity K D m) (s : PlacedStep m B out child) (q : s.Index e)
    (next : Finset (HyperbolicHost I)) (h : ℝ)
    (hs : ∀ v, Catalog.relative out ((s.result e q).site v) ∈ next)
    (hl : ∀ c, (s.result e q).charged c = true →
      dist ((s.result e q).site ((s.result e q).pack.layout.src c))
        ((s.result e q).site ((s.result e q).pack.layout.dst c)) ≤ 2*h) :
    Catalog.PlacedAt next h (s.result e q) := by
  refine ⟨hs,hl,?_⟩
  intro c _
  let p := s.result e q
  exact (surfaceMidpoint_dist (p.site (p.pack.layout.src c)) (p.site (p.pack.layout.dst c))).1.le

namespace Adaptive

/-- A single uniform geometric preparation at a given finite catalog. Its
exact pack operation, both measured inputs and the next preparation are
available at every sufficiently deep quotient and every positive fan-in. -/
structure StageTemplate (e : PaidIdentity K D m) (I : Type) [Fintype I] (hCap hSaving ν : ℝ)
    (S : Finset (HyperbolicHost I)) where
  /-- Fixed relative addresses in one tile. -/
  Bin : Type
  /-- Enumeration of these addresses. -/
  [finite : Fintype Bin]
  /-- Relative-site catalog prepared for all possible joint output histograms. -/
  nextSites : Finset (HyperbolicHost I)
  /-- Chosen Hecke word length. -/
  word : ℕ
  /-- Lowest admissible output depth. -/
  floor : ℕ
  /-- Multiplier from minimum positive segment length. -/
  meanFactor : ℝ
  /-- Multiplier for the chosen independent whole-pack motions. -/
  motionFactor : ℝ
  /-- Both multipliers can be used in the stage calibration. -/
  nonneg : 0 ≤ meanFactor ∧ 0 ≤ motionFactor
  /-- Realize a geometric operation on these exact children, together with
  its measured motion data and closure on every attained histogram. -/
  run : ∀ (d : ℕ), floor ≤ d → ∀ {k : ℕ} (hk : 0 < k) {P : Type} {bits : P → ℕ}
    (child : Fin k → PlacedPack D P bits K I (d+2*word)),
    (∀ i, Catalog.PlacedAt S hCap (child i)) →
    ∃ s : PlacedStep m Bin d child, Nonempty (Measurements s hk hSaving ν meanFactor motionFactor) ∧
      ∀ q : s.Index e, Catalog.PlacedAt nextSites hCap (s.result e q)

attribute [instance] StageTemplate.finite

variable {hCap hSaving ν : ℝ} {e : PaidIdentity K D m} {S : Finset (HyperbolicHost I)}

/-- Use a stage on the actual scheduled input level by transporting along
the exact integer depth equation. -/
theorem StageTemplate.atLevel (t : StageTemplate e I hCap hSaving ν S) {old next : ℕ}
    (hlevel : old = next+2*t.word) (hfloor : t.floor ≤ next) (hk : 0 < k)
    (child : Fin k → PlacedPack D P bits K I old) (hchild : ∀ i, Catalog.PlacedAt S hCap (child i)) :
    ∃ s : PlacedStep m t.Bin next child, Nonempty (Measurements s hk hSaving ν t.meanFactor t.motionFactor) ∧
      ∀ q : s.Index e, Catalog.PlacedAt t.nextSites hCap (s.result e q) := by
  subst old
  exact t.run next hfloor hk child hchild

/-- The finite chain of chosen stage preparations. -/
abbrev StagePath (b : ℕ) (e : PaidIdentity K D m) (I : Type) [Fintype I] (hCap hSaving ν : ℝ) :=
  PreparedPath b (StageTemplate e I hCap hSaving ν) (fun _ t => t.nextSites)

variable {b : ℕ} (path : StagePath b e I hCap hSaving ν)

/-- Install one measured program directly on the stage states selected by
the prepared path. Every successor is the original physical result of
its chosen step. All thresholds hold simultaneously for this schedule. -/
theorem StagePath.exists_program (terminal last : ℕ) (hk : 0 < k)
    (hf : ∀ i : Fin b, (path.pattern i).floor ≤ Levels.level (fun j => (path.pattern j).word) terminal last (i.val+1)) :
    let levels := Levels.level (fun i => (path.pattern i).word) terminal last
    let good := fun n (p : PlacedPack D (Port k P n) (width bits k n) K I (levels n)) =>
      Catalog.PlacedAt (path.catalog n) hCap p
    ∃ F : Program (B := fun i => (path.pattern i).Bin) e (fun n (p : Program.Prepared good n) => p.val),
      (∀ i c, Nonempty (Measurements (F.step i c) hk hSaving ν (path.pattern i).meanFactor
        (path.pattern i).motionFactor)) ∧
      ∀ i c q, (F.advance i c q).val = (F.step i c).result e q := by
  intro levels good
  have H (i : Fin b) (c : Fin k → Program.Prepared good i.val) :=
    (path.pattern i).atLevel (Levels.step_depth (fun j => (path.pattern j).word) terminal last i)
      (hf i) hk (fun j => (c j).val) (fun j => (c j).property)
  choose step measure closed using H
  have ok (i : Fin b) (c : Fin k → Program.Prepared good i.val) (q : (step i c).Index e) :
      good (i.val+1) ((step i c).result e q) := by
    change Catalog.PlacedAt (path.catalog (i.val+1)) hCap _
    rw [path.next i]
    exact closed i c q
  exact ⟨Program.ofClosed e good step ok,measure,fun _ _ _ => rfl⟩

end Adaptive
end Shortening

end BorderVNP
end Computability
end OAI
