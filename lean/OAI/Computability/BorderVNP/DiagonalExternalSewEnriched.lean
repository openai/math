import OAI.Computability.BorderVNP.DiagonalExternalSewNormalized
import OAI.Computability.BorderVNP.DiagonalExternalSewEpoch
import OAI.Computability.BorderVNP.PackedHistoryNormalizedEnriched

/-! # Original vertex addresses on enriched public histograms -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Adaptive Packing Cover Epoch Epoch.Round CellEntries PackedHistoryCircuit.Normalized
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] {bits : P → ℕ} {e : PaidIdentity K D m}

/-- The saved cable numbering gives the actual layout isomorphism of each
branch, even when the state keeps additional data beyond its placed pack. -/
noncomputable def namesStorage {k b : ℕ} {I : Type} [Fintype I] {A : ℕ → Type*}
    {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (F : PackedHistoryCircuit.Normalized.Program (B := B) e view) (names : F.SaveNames) :
    DenseReplay.Saved F := fun i c q => by
  rw [names.stored i c q]
  exact Storage.dense _ (names.number i c q)

variable {d : ℕ} {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {A : ℕ → Type*}
    {view : S.GeometricView d P bits A} (F : S.EnrichedProgram d view)
    (flat : Fin (S.fanIn^S.rounds) → A 0)
    (initial : ∀ i, InitialSites (view 0 (flat i)) S.budget S.radius_pos)
    {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
    (originalPack : ∀ i, (initial i).pack = input i)

/-- Installation sends an original host to its old endpoint in the
particular routed equality subdivision chosen for this public input. -/
noncomputable def enrichedInstalledHosts (i : Fin (S.fanIn^S.rounds)) :
    Retains (input i).layout (view 0 (flat i)).pack.layout := by
  let data := initial i
  let original := Retains.ofEq (congrArg Pack.layout (originalPack i).symm)
  let installed := Retains.ofEq (congrArg (fun p => p.pack.layout) data.realizes.symm)
  exact original.trans ((Retains.subdivide data.pack.layout (data.routes.routes S.radius)).trans installed)

/-- The address of each original host in the stored output of this
particular enriched histogram, including its true leaf subdivision. -/
noncomputable def enrichedHistoryHosts (names : F.SaveNames) (q : F.Hist flat) :
    Retains (parallelPacks input).layout (flattenPack S.rounds (F.terminal flat q).pack).layout :=
  (Retains.parallel (enrichedInstalledHosts flat initial originalPack)).trans
    (normalizedHosts F (namesStorage F names) flat q)

variable [Fintype P] {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget}

/-- Original addresses on the output returned for the given native index,
with the initial layout and leaf names read from this execution itself. -/
noncomputable def enrichedEpochHosts {F : S.EnrichedProgram d view}
    (run : SiteSchedule.EnrichedExecution F input route) (names : F.SaveNames) (q : F.Hist run.flat) :
    Retains (parallelPacks input).layout (flattenPack S.rounds (F.terminal run.flat q).pack).layout :=
  enrichedHistoryHosts F run.flat run.initialSites run.originalPack names q

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
