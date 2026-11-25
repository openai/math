import OAI.Computability.BorderVNP.PackedRetainedFields
import OAI.Computability.BorderVNP.PackedEnrichedHistoryRecords
import OAI.Computability.BorderVNP.DiagonalExternalSewEnrichedOuter

/-! # The original box payload at its terminal named site

The actual gate-selected outer history sends each original bundle and tile
to an injectively retained vertex. Its exact metadata survives there. This
connects per-site record caps to the private deliveries for the original
box descriptions, even with adaptive intermediate row directories.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Packing Adaptive PublicCapacity PhysicalEpochs
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u

variable {D m start T : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)]
    {w : ℕ → ℕ → ℕ} {good : ∀ t, EnrichedOuter.State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start} (M : EnrichedOuter.Machine.{_,u} deep good V w)

omit [∀ t, Fintype (W t)] in
private theorem transportEnriched {t : ℕ} (child : Fin (fan S) → Admissible good t)
    (data : ∀ i, RecordData (child i).val.pack.layout) {Z Y : ProfileSum (Admissible good (t+1))} (eq : Z = Y)
    (step : ReturnedFields child data Y)
    (sites : ∀ j : Y.Index, Retains (parallelPacks fun i => (child i).val.pack).layout (Y.term j).val.pack.layout)
    (h : ∀ j i v, boxFields (step.field j) ((sites j).site ⟨i,v⟩) = boxFields (data i) v) :
    ∀ j : Z.Index, ∀ i v, boxFields (((congrArg (fun z => ReturnedFields child data z) eq).mpr step).field j)
      (((congrArg (fun (z : ProfileSum (Admissible good (t+1))) =>
        ∀ j : z.Index, Retains (parallelPacks fun i => (child i).val.pack).layout (z.term j).val.pack.layout) eq).mpr sites j).site ⟨i,v⟩) =
      boxFields (data i) v := by cases eq; exact h

/-- The enriched machine preserves the fields at each input vertex in the
chosen child tuple, including its actual before/after public row sorts. -/
theorem enrichedStep_fields (t : ℕ) (ht : t<T) (child : Fin (fan S) → Admissible good t)
    (data : ∀ i, RecordData (child i).val.pack.layout) :
    ∀ q : (M.epoch t child).Index, ∀ i v, boxFields ((M.nodeRecords t child data).field q)
      ((enrichedStepHosts M ht child q).site ⟨i,v⟩) = boxFields (data i) v := by
  simp only [EnrichedOuter.Machine.nodeRecords,enrichedStepHosts,EnrichedOuter.Machine.epoch,dite_eq_left ht]
  apply transportEnriched child data (dite_eq_left ht)
  intro q i v
  let E := M t ht
  let run := E.run child
  exact originalFields E.F E.saveNames run.flat run.initialSites run.originalPack data q i v

variable (bottom : Admissible good 0) (base : RecordData bottom.val.pack.layout)

set_option maxHeartbeats 1200000 in
/-- Both inherited record counts at the true terminal image of a nested
bottom vertex. -/
theorem enrichedNested_fields (t : ℕ) (ht : t ≤ T) (q : (packHistory bottom M.epoch t).Index)
    (v : (parallelLeaves (fun _ : Unit => bottom.val.pack) t
      (leavesEquiv (fan S) Unit t fun _ => ())).layout.Site) :
    let z := originalNames (fun _ : Unit => bottom.val.pack) t (fun _ => ()) v
    boxFields (M.historyFields bottom base t q) ((enrichedNestedHosts M bottom t ht q).site v) = boxFields base z.2 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rcases v with ⟨i,v⟩
    let H := packHistory bottom M.epoch t
    let c := fun i : Fin (fan S) => H.term (q.1 i)
    let r := fun i => M.historyFields bottom base t (q.1 i)
    let h := enrichedNestedHosts M bottom t (by omega) (q.1 i)
    exact (enrichedStep_fields M t (by omega) c r q.2 i (h.site v)).trans (ih (by omega) (q.1 i) v)

/-- Each physical description attached to an original bundle/site arrives
at a final site carrying the same private payload and prior descriptor count. -/
theorem enrichedOriginal_fields (q : (packHistory bottom M.epoch T).Index)
    (i : Fin ((fan S)^T)) (v : bottom.val.pack.layout.Site) :
    boxFields (M.historyFields bottom base T q) ((enrichedOuterHosts M bottom q).site ⟨i,v⟩) = boxFields base v := by
  let order := originalNames (fun _ : Unit => bottom.val.pack) T (fun _ : Fin ((fan S)^T) => ())
  let z : (parallelPacks (fun _ : Fin ((fan S)^T) => bottom.val.pack)).layout.Site := ⟨i,v⟩
  have he := enrichedNested_fields M bottom base T le_rfl q (order.symm z)
  change _ = boxFields base (order (order.symm z)).2 at he
  rw [order.apply_symm_apply] at he
  exact he

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
