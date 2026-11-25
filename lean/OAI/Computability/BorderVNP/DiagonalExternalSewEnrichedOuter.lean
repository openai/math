import OAI.Computability.BorderVNP.DiagonalExternalSewEnriched
import OAI.Computability.BorderVNP.PackedHistoryNormalizedMachine

/-! # Host ancestry on the complete assigned outer state -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Epoch Epoch.Round Cover Shortening Adaptive Packing PackedHistoryCircuit
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u

variable {D m start T : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)]
    {w : ℕ → ℕ → ℕ} {good : ∀ t, EnrichedOuter.State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start} (M : EnrichedOuter.Machine.{0,u} deep good V w)

/-- The site injection on the actual outer node uses the branch index
of its inner program on the supplied complete child states. -/
noncomputable def enrichedStepHosts {n : ℕ} (hn : n<T) (child : Fin (fan S) → Admissible good n) :
    ∀ q : (M.epoch n child).Index, Retains (parallelPacks fun i => (child i).val.pack).layout
      ((M.epoch n child).term q).val.pack.layout := by
  unfold Machine.epoch
  rw [dite_eq_left hn]
  exact enrichedEpochHosts ((M n hn).run child) (M n hn).saveNames

variable (bottom : Admissible good 0)

/-- Prefix the original host's address by its child number at each
active outer node and follow the particular inner histogram there. -/
noncomputable def enrichedNestedHosts :
    (n : ℕ) → (hn : n ≤ T) → (q : (packHistory bottom M.epoch n).Index) →
    Retains (parallelLeaves (fun _ : Unit => bottom.val.pack) n (leavesEquiv (fan S) Unit n fun _ => ())).layout
      ((packHistory bottom M.epoch n).term q).val.pack.layout
  | 0, _, _ => Retains.id _
  | n+1, hn, q => by
    let H := packHistory bottom M.epoch n
    let child := fun i : Fin (fan S) => H.term (q.1 i)
    exact (Retains.parallel fun i => enrichedNestedHosts n (Nat.le_of_succ_le hn) (q.1 i)).trans
      (enrichedStepHosts M (Nat.lt_of_succ_le hn) child q.2)

/-- Original host addresses in the flattened physical terminal of the exact
assigned geometry history, in the public row-major order of the copies. -/
noncomputable def enrichedOuterHosts (q : (packHistory bottom M.epoch T).Index) :
    Retains (parallelPacks fun _ : Fin ((fan S)^T) => bottom.val.pack).layout
      (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout :=
  (flatOriginal (fun _ : Unit => bottom.val.pack) T (fun _ => ())).trans
    (enrichedNestedHosts M bottom T le_rfl q).flat

variable (q : (packHistory bottom M.epoch T).Index)

/-- Actual final cover tile reached by the host of an original bottom box. -/
noncomputable def enrichedOriginTile (i : Fin ((fan S)^T)) (v : bottom.val.pack.layout.Site) :=
  let state := ((packHistory bottom M.epoch T).term q).val
  reduceMove (depth S start T) (state.route.origin ((enrichedOuterHosts M bottom q).site ⟨i,v⟩))

/-- The original private host and the flattened external port of its copy
address the same tile of the returned route. -/
theorem enrichedOriginTile_attach (i : Fin ((fan S)^T)) (p : P) :
    let state := ((packHistory bottom M.epoch T).term q).val
    enrichedOriginTile M bottom q i (bottom.val.pack.layout.attach p) =
      reduceMove (depth S start T) (state.route.origin ((flattenPack T state.pack).layout.attach (i,p))) := by
  let hosts := enrichedOuterHosts M bottom q
  let state := ((packHistory bottom M.epoch T).term q).val
  exact congrArg (fun v => reduceMove _ (state.route.origin v)) (hosts.attach (i,p)).symm

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
