import OAI.Computability.BorderVNP.ShortenSiteProgram
import OAI.Computability.BorderVNP.ShortenEpochRoundFlatSites
import OAI.Computability.BorderVNP.ShortenActualRecordTemplate

/-!
# The execution underlying the physical site epoch

Keep the actual adaptive program, its measured steps and local record
bounds, the tensor-preserving input subdivisions, and the rounded terminal
histograms together. A single program at a given depth and external port
list acts on every possible tuple of input networks and site placements.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Cover Epoch Epoch.Round Adaptive Packing Catalog Filter
open scoped Classical Topology BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m b k : ℕ} [NeZero D] {K : Type*} [Field K] {P : Type} {bits : P → ℕ}
variable {e : PaidIdentity K D m} {h H ν : ℝ}

/-- The actual flat summands and site routes returned by a whole epoch on the
specified family of arbitrary valued input packs. -/
structure SiteExpansion {I P : Type} [Fintype I] {bits : P → ℕ} {k b inputDepth outputDepth : ℕ}
    (hk : 0 < k) (input : Fin (k^b) → Pack D P bits K) {L : ℝ}
    (route : ∀ i, SiteRoutes (input i) I inputDepth L) (weight E : ℝ) where
  /-- Number of attained complete joint histograms. -/
  terms : ℕ
  /-- The physical site packs indexed by the attained histograms. -/
  pack : Fin terms → Pack D (Fin (k^b) × P) (fun z => bits z.2) K
  /-- The actual surviving site moves at the lower level. -/
  routes : ∀ j, SiteRoutes (pack j) I outputDepth L
  /-- All entries of the original formal tensor are preserved. -/
  tensor : ∀ x, (parallelPacks input).tensor x = ∑ j, (pack j).tensor x
  /-- The width and incidence of every individual returned network obey (6.1). -/
  bound : ∀ j, (routes j).potential weight / (k:ℝ)^b ≤
    maximumLeaf (b := b) hk id (fun i => (route i).potential weight)/2 +
      E * Fintype.card (I → Deck (inputDepth+1))

/-- The physically selected program for this cover level and external slot list.
It is fixed before the tuple of input circuits and their field entries. -/
structure SiteMachine (path : StagePath b e (Cube D) h H ν) (C : Fin b → ℕ)
    (last high : ℕ) (hk : 0 < k) (P : Type) (bits : P → ℕ) where
  /-- Actual public histogram tree with the prepared site predicate at every node. -/
  F : Program (B := fun i => (path.pattern i).Bin) e (fun j (p : path.State P bits k last high j) => p.val)
  /-- Each chosen physical motion has its geometric and variance measurements. -/
  measured : ∀ i c, Nonempty (PlacedStep.Measurements (F.step i c) hk H ν
    (path.pattern i).meanFactor (path.pattern i).motionFactor)
  /-- The record factor applies to this same motion and all its actual profile outputs. -/
  records : ∀ i c, (F.step i c).RecordFactor e (C i)
  /-- A stored output is literally the sewn network on the selected branch. -/
  stored : ∀ i c q, (F.advance i c q).val = (F.step i c).result e q

variable {path : StagePath b e (Cube D) h H ν} {C : Fin b → ℕ} {last high : ℕ} {hk : 0 < k}
variable (machine : SiteMachine path C last high hk P bits)

/-- One actual input tuple, its equality subdivision, every true joint histogram,
and the final physical site move on that histogram. -/
structure SiteExecution [Fintype P] {low : ℕ} {L : ℝ}
    (hh : 0 < h) (input : Fin (k^b) → Pack D P bits K) (route : ∀ i, SiteRoutes (input i) (Cube D) high L)
    (weight E A Cout : ℝ) (cap : ℕ) where
  /-- The actual leaf states installed on the recursively nested external labels. -/
  flat : Fin (k^b) → path.State P bits k last high 0
  /-- Each stored leaf is the true geodesic equality subdivision of this routed network. -/
  initialSites : ∀ i, InitialSites (flat i).val L hh
  /-- Underlying algebraic input networks match the given tuple entry by entry. -/
  originalPack : ∀ i, (initialSites i).pack = input i
  /-- Reindexing the depth of the given sites preserves even their actual integral routing data. -/
  originalRoutes : ∀ i, HEq (initialSites i).routes (route i)
  /-- The selected site motion on each true terminal histogram before flattening. -/
  out : ∀ i : machine.F.Hist flat, SiteOutput (machine.F.terminal flat i) low L A Cout cap
  /-- Equation (6.1) for these very motions and terminal branches. -/
  bound : ∀ i, (out i).routes.potential weight / (k:ℝ)^b ≤
    maximumLeaf hk id (fun j => (route j).potential weight)/2 + E*Fintype.card (Cube D → Deck (high+1))
  /-- Equality on the original external port tuple, for the same histograms. -/
  tensor : ∀ x, (parallelPacks input).tensor x =
    ∑ i : machine.F.Hist flat, (flattenPack b (machine.F.terminal flat i).pack).tensor x

namespace SiteExecution

variable [Fintype P] {low : ℕ} {L weight E A Cout : ℝ} {cap : ℕ} {hh : 0 < h}
variable {input : Fin (k^b) → Pack D P bits K} {route : ∀ i, SiteRoutes (input i) (Cube D) high L}
variable {machine} (run : SiteExecution (low := low) machine hh input route weight E A Cout cap)

/-- Row-major finite enumeration of the actual adaptive histograms. -/
noncomputable def enum := (Fintype.equivFin (machine.F.Hist run.flat)).symm

/-- Forget the internal profiles while retaining the exact flat output packs and routes. -/
noncomputable def expansion : SiteExpansion (outputDepth := low) hk input route weight E where
  terms := Fintype.card (machine.F.Hist run.flat)
  pack j := flattenPack b (machine.F.terminal run.flat (run.enum j)).pack
  routes j := (run.out (run.enum j)).routes.flatten
  tensor x := (run.tensor x).trans (run.enum.sum_comp (fun i => (flattenPack b (machine.F.terminal run.flat i).pack).tensor x)).symm
  bound j := run.bound (run.enum j)

end SiteExecution

end Shortening

end BorderVNP
end Computability
end OAI
