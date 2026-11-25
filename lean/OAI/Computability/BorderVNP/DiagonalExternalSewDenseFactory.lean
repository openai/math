import OAI.Computability.BorderVNP.DiagonalExternalSewNormalized
import OAI.Computability.BorderVNP.DiagonalExternalSewFactoryRetention
import OAI.Computability.BorderVNP.DiagonalExternalSewEpoch
import OAI.Computability.BorderVNP.DiagonalSpecializedDenseSiteEpoch
import OAI.Computability.BorderVNP.PackedDenseFactory

/-! # Site ancestry on the actual dense site schedule and every outer branch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Adaptive Packing Packing.PhysicalEpochs Cover Epoch Epoch.Round CellEntries
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m d : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e}
    {M : PackedHistoryCircuit.Normalized.SiteMachine S d P bits}
    {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
    {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget}
    (run : PackedHistoryCircuit.Normalized.SiteExecution S M input route)

/-- Installation in the dense site machine keeps each original vertex
through the measured equality subdivision of that particular input pack. -/
noncomputable def denseInstalledHosts (i : Fin (S.fanIn^S.rounds)) :
    Retains (input i).layout (run.flat i).val.pack.layout := by
  let data := run.initialSites i
  let original := Retains.ofEq (congrArg Pack.layout (run.originalPack i).symm)
  let stored := Retains.ofEq (congrArg (fun p => p.pack.layout) data.realizes.symm)
  exact original.trans ((Retains.subdivide data.pack.layout (data.routes.routes S.radius)).trans stored)

/-- The complete dense site epoch keeps the original flat tuple's host
addresses on each of its actual sorted and stored output networks. -/
noncomputable def denseEpochHosts (j : Fin run.expansion.terms) :
    Retains (parallelPacks input).layout (run.expansion.pack j).layout :=
  (Retains.parallel (denseInstalledHosts run)).trans
    (normalizedHosts M.F (DenseSiteReplay.storage M) run.flat (run.enum j))

variable (program : Factory.Dense.Programs S) {start T : ℕ}
    (deep : (Factory.ofDenseSchedule program).floor+1+(Factory.ofDenseSchedule program).drop*T ≤ start)

/-- The chosen active outer profile is the finite output of the physical
dense machine on that tuple. -/
noncomputable def denseFactoryStepHosts : FactoryStepHosts (bits := bits) (Factory.ofDenseSchedule program) deep := by
  intro n hn child
  unfold Factory.epoch
  rw [dite_eq_left hn]
  let F := Factory.ofDenseSchedule program
  let actual := program.run _ (F.levels deep hn).1 _ _ (fun i => (child i).pack)
    (fun i => reindexRoutes (F.levels deep hn).2.2.symm (child i).route)
  exact denseEpochHosts actual

/-- The retained vertex map for every attained profile history of the
actual dense factory, on its true flattened terminal network. -/
noncomputable def denseOuterHosts (bottom : (Factory.ofDenseSchedule program).State bits start 0)
    (q : ((Factory.ofDenseSchedule program).histories deep bottom T).Index) :
    Retains (parallelPacks (fun _ : Fin ((Factory.ofDenseSchedule program).fan^T) => bottom.pack)).layout
      (flattenPack T (((Factory.ofDenseSchedule program).histories deep bottom T).term q).pack).layout :=
  factoryOuterHosts (Factory.ofDenseSchedule program) deep (denseFactoryStepHosts program deep) bottom q

variable (bottom : (Factory.ofDenseSchedule program).State bits start 0)
variable (q : ((Factory.ofDenseSchedule program).histories deep bottom T).Index)

/-- The actual final cover tile at which this original bottom box is located. -/
noncomputable def denseOriginTile (i : Fin ((Factory.ofDenseSchedule program).fan^T)) (v : bottom.pack.layout.Site) :=
  let F := Factory.ofDenseSchedule program
  let state := (F.histories deep bottom T).term q
  reduceMove (F.depth start T) (state.route.origin ((denseOuterHosts program deep bottom q).site ⟨i,v⟩))

/-- Delivery to the final host of an original grouped port uses the same
tile as delivery to its original private box. -/
theorem denseOriginTile_attach (i : Fin ((Factory.ofDenseSchedule program).fan^T)) (p : P) :
    let F := Factory.ofDenseSchedule program
    let state := (F.histories deep bottom T).term q
    denseOriginTile program deep bottom q i (bottom.pack.layout.attach p) =
      reduceMove (F.depth start T) (state.route.origin ((flattenPack T state.pack).layout.attach (i,p))) := by
  let hosts := denseOuterHosts program deep bottom q
  let state := ((Factory.ofDenseSchedule program).histories deep bottom T).term q
  exact congrArg (fun v => reduceMove _ (state.route.origin v)) (hosts.attach (i,p)).symm

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
