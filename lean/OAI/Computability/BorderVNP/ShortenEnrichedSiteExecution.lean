import OAI.Computability.BorderVNP.ShortenDenseExecution

/-!
# Site executions on states retaining every public pin

The placement of a state is a projection of the stored public data. The
stage may examine all those data when choosing rows and motions. This
execution therefore uses the histogram of the actual program with its
complete state, even when two different pin arrays have identical geometry.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Epoch Epoch.Round Cover Cover.Frame Shortening Packing Catalog Adaptive
open scoped Classical Topology BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m}
    (S : SiteSchedule e) (d : ℕ)

namespace SiteSchedule

/-- The absolute starting level and every source cutoff permit the actual
compiled preparation. -/
def FitsLevels : Prop :=
  S.level d 0 = S.high d ∧ ∀ i : Fin S.rounds, (S.source.pattern i).floor ≤ S.level d (i.val+1)

/-- The input subdivision, with its original routes, values and potentials,
is available for any choice of incoming public site networks. -/
def HasLeaves : Prop :=
  ∀ {P : Type} {bits : P → ℕ} (input : Fin (S.fanIn^S.rounds) → Pack D P bits K)
    (route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget),
    ∃ f : Fin (S.fanIn^S.rounds) → S.State d P bits 0,
    ∃ init : ∀ i, InitialSites (f i).val S.budget S.radius_pos,
      (∀ i, (init i).pack = input i) ∧ (∀ i, (init i).routes.potential S.weight = (route i).potential S.weight) ∧
      ∀ i, HEq (init i).routes (route i)

/-- The complete data of any public state are accessible to the program,
whose geometry is read through this projection. -/
abbrev GeometricView (P : Type) (bits : P → ℕ) (states : ℕ → Type u) :=
  ∀ j, states j → PlacedPack D (Port S.fanIn P j) (width bits S.fanIn j) K (Cube D) (S.level d j)

/-- The normalized program whose branching depends on the actual enriched
child data and saves its corresponding state on each individual branch. -/
abbrev EnrichedProgram {P : Type} {bits : P → ℕ} {states : ℕ → Type u}
    (view : S.GeometricView d P bits states) := Program (B := fun i => (S.source.pattern i).bins.Bin) e view

variable {S d} {P : Type} {bits : P → ℕ} {states : ℕ → Type u}
    {view : S.GeometricView d P bits states} (F : S.EnrichedProgram d view)
    (flat : Fin (S.fanIn^S.rounds) → states 0)
    (initial : ∀ i, InitialSites (view 0 (flat i)) S.budget S.radius_pos)
    (σ : F.Hist flat → Cube D → Fin S.motions)

/-- The final sites at the prescribed motion, with exact retained addresses,
charged slots, integral moves, potential and free-label tensor. -/
structure EnrichedOutput [Fintype P] where
  /-- Routes assigned to each actual enriched terminal state. -/
  out : ∀ i, SiteOutput (F.terminal flat i) (d+1) S.budget S.finalWidth S.finalConcentration S.finalCap
  origins : ∀ i v, reduceMove (d+1) ((out i).routes.origin v) =
    productAddress (d+1) (S.terminalMove (F.terminal flat i) (σ i) v)
  charges : ∀ i c, (out i).routes.active c ↔
    let p := F.terminal flat i
    p.active c ∧ productAddress (d+1) (S.terminalMove p (σ i) (p.pack.layout.src c)) ≠
      productAddress (d+1) (S.terminalMove p (σ i) (p.pack.layout.dst c))
  first : ∀ i, (out i).routes.FirstAligned
  bound : ∀ i, (out i).routes.potential S.weight / (S.fanIn : ℝ)^S.rounds ≤
    maximumLeaf S.positiveFanIn id (fun j => (initial j).routes.potential S.weight)/2 +
      S.error*Fintype.card (Cube D → Deck (S.high d+1))
  tensor : ∀ x, (parallelPacks (fun j => (initial j).pack)).tensor x =
    ∑ i : F.Hist flat, (flattenPack S.rounds (F.terminal flat i).pack).tensor x

/-- The same fixed calibration works for every richer representation whose
actual stages satisfy the physical measurements and whose public saves
use their actual cable directories. -/
def RunsEnriched (S : SiteSchedule e) (d : ℕ) : Prop :=
  ∀ {P : Type} [Fintype P] {bits : P → ℕ} {states : ℕ → Type u} (view : S.GeometricView d P bits states)
    (F : S.EnrichedProgram d view),
    (∀ a, PlacedAt (S.source.catalog S.rounds) S.radius (view S.rounds a)) →
    (∀ i c, Nonempty (Stage.Measurements (F.stage i c) S.positiveFanIn S.saving S.tolerance
      (S.source.pattern i).mean (S.source.pattern i).motion)) →
    F.SaveNames →
    ∀ (flat : Fin (S.fanIn^S.rounds) → states 0) (initial : ∀ i, InitialSites (view 0 (flat i)) S.budget S.radius_pos)
      (σ : F.Hist flat → Cube D → Fin S.motions), (∀ i, S.Minimizes (F.terminal flat i) (σ i)) →
      Nonempty (EnrichedOutput F flat initial σ)

end SiteSchedule
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
