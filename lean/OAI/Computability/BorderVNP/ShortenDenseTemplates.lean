import OAI.Computability.BorderVNP.ShortenDenseEpoch
import OAI.Computability.BorderVNP.ShortenDenseCatalog
import OAI.Computability.BorderVNP.ShortenCatalogEpoch

/-!
# Prepared geometry on the stable public cable order

Every possible sparse row embedding names the merged input before interval
allocation. A prepared stage returns its actual matched crossing, including
the given row capacity and names. The next relative catalog also survives
reindexing the attained output by the public storage directory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Epoch Cover Shortening Packing Catalog
open scoped Classical

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K]
    {I P : Type} [Fintype I] {bits : P → ℕ} {e : PaidIdentity K D m}

/-- Finite geometric constants and motion tables at one publicly sorted stage. -/
structure StageTemplate (e : PaidIdentity K D m) (I : Type) [Fintype I] (hCap hSaving ν : ℝ)
    (S : Finset (HyperbolicHost I)) where
  /-- Relative bin names inside one tile. -/
  Bin : Type
  /-- All such names have a fixed finite enumeration. -/
  [finite : Fintype Bin]
  /-- The uniformly valid next list of relative sites. -/
  nextSites : Finset (HyperbolicHost I)
  /-- Hecke word cutoff for this round. -/
  word : ℕ
  /-- Lowest admissible output level. -/
  floor : ℕ
  /-- Bound for the normalized ideal bin mean. -/
  meanFactor : ℝ
  /-- Bound for the chosen whole-pack motion deviation. -/
  motionFactor : ℝ
  /-- Both quantitative coefficients are nonnegative. -/
  nonneg : 0 ≤ meanFactor ∧ 0 ≤ motionFactor
  /-- Realize the stage on any actual ordered input, with closure on every histogram. -/
  run : ∀ (d : ℕ), floor ≤ d → ∀ {k : ℕ} (hk : 0 < k) {P : Type} {bits : P → ℕ}
    (child : Fin k → PlacedPack D P bits K I (d+2*word)), (∀ i, PlacedAt S hCap (child i)) →
    ∀ (rows : ℕ) (slot : (raw child).layout.Edge ↪ Fin rows),
      ∃ s : Stage m Bin d child, s.rowCount = rows ∧ (∀ x, (s.slot x).val = (slot x).val) ∧
        Nonempty (Stage.Measurements s hk hSaving ν meanFactor motionFactor) ∧
        ∀ q : s.Index e, PlacedAt nextSites hCap (s.result e q)

attribute [instance] StageTemplate.finite

variable {hCap hSaving ν : ℝ}

/-- Ordered sequence of preparations, fixed before the fan-in and absolute level. -/
abbrev StagePath (b : ℕ) (e : PaidIdentity K D m) (I : Type) [Fintype I] (hCap hSaving ν : ℝ) :=
  Adaptive.PreparedPath b (StageTemplate e I hCap hSaving ν) (fun _ t => t.nextSites)

namespace StagePath

variable (path : StagePath b e I hCap hSaving ν)

/-- Cover level at stage j, including the final site-rounding drop. -/
def depth (last high j : ℕ) :=
  let word := fun i => (path.pattern i).word
  Adaptive.Levels.level word (high - Adaptive.Levels.totalDrop word last) last j

/-- A sufficient uniform starting depth for all rounds. -/
def threshold (last lastFloor : ℕ) :=
  Adaptive.Levels.totalDrop (fun i => (path.pattern i).word) last + (lastFloor + ∑ i, (path.pattern i).floor)

/-- The physical states, each accompanied by its prepared geometric validity. -/
abbrev State (P : Type) (bits : P → ℕ) (k last high j : ℕ) :=
  {p : PlacedPack D (Adaptive.Port k P j) (Adaptive.width bits k j) K I (path.depth last high j) //
    PlacedAt (path.catalog j) hCap p}

end StagePath

variable {d : ℕ} (p : PlacedPack D P bits K I d)

omit [NeZero D] [Field K] in
/-- Reindexing all cables at their public stored row preserves the geometric
input predicate, including every distinct charged midpoint and the common cap. -/
theorem placedAt_dense {S : Finset (HyperbolicHost I)} (hp : PlacedAt S hCap p)
    {rows : ℕ} (slot : p.pack.layout.Edge ↪ Fin rows) : PlacedAt S hCap (p.dense slot) := by
  let f := Names.denseSlot p.pack.layout slot
  refine ⟨hp.sites,?_,?_⟩
  · intro e he
    obtain ⟨x,rfl⟩ := f.surjective e
    have hs := p.dense_endpoints slot x
    have ha := (p.dense_marks slot x).1
    rw [hs.1,hs.2]
    exact hp.short x (ha ▸ he)
  · intro e he
    obtain ⟨x,rfl⟩ := f.surjective e
    have hs := p.dense_endpoints slot x
    have ha := p.dense_marks slot x
    obtain ⟨hc,hne⟩ := ((p.dense slot).active_iff _).mp he
    rw [hs.1,hs.2] at hne
    rw [ha.2,hs.1,hs.2]
    exact hp.midpoint x ((p.active_iff x).mpr ⟨ha.1 ▸ hc,hne⟩)

end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
