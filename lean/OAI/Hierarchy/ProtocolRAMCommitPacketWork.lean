import OAI.Hierarchy.ProbeStripRowWork
import OAI.Hierarchy.ProtocolRAMBatchResources
import OAI.Hierarchy.ProtocolRAMRepairHistogram

namespace OAI
/-! # Uniform packet credits, debits and broadcasts at a fixed alphabet and arity -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open PurchaseStage StripDirectory RowResources

private structure PacketWork {q d : ℕ} (L : Dispatch) (B : Repair q d) (bank : Bank) (K : ℕ) : Prop where
  credit : ∀ i, ((enabledBatch L B).wire (B.wire i)).work ≤ K
  debit : ∀ i, (RepairHistogram.debit (enabledBatch L B) i).work ≤ K
  broadcast : (RepairHistogram.broadcastTerm (enabledBatch L B) bank).work ≤ K

private theorem packet_work_exists (q d M U : ℕ) : ∃ K, ∀ (L : Dispatch) (B : Repair q d)
    (bank : Bank), RowWork B U → B.batch.maxWidth = M → PacketWork L B bank K := by
  classical
  let I := {t : (Dispatch × Repair q d) × Bank // RowWork t.1.2 U ∧ t.1.2.batch.maxWidth = M}
  let b (i : I) := enabledBatch i.1.1.1 i.1.1.2
  have batch : BatchOperands b M :=
    ⟨fun i => i.2.2, ⟨U,fun i => i.2.1.packet⟩,RowResources.row,
      fun j => ⟨U,fun i => i.2.1.fields j⟩,fun j => ⟨U,fun i => i.2.1.stocks j⟩,
      fun j => ⟨U,fun i => i.2.1.prices j⟩⟩
  have credits (j : Fin d) : Bounded (fun i => (b i).wire (i.1.1.2.wire j)) :=
    batch.width _ (fun t => ⟨U,fun i => i.2.1.wires j t⟩)
  have debits (j : Fin d) : Bounded (fun i => RepairHistogram.debit (b i) j) :=
    batch.selection (batch.hist (batch.need j) (RowResources.lit _)) (RowResources.lit _)
  have cast : Bounded (fun i => RepairHistogram.broadcastTerm (b i) i.1.2) :=
    batch.selection (batch.hist (RowResources.load _ batch.packet) (RowResources.lit _)) (RowResources.lit _)
  let c := Finset.univ.sup (fun j => Classical.choose (credits j))
  let d' := Finset.univ.sup (fun j => Classical.choose (debits j))
  obtain ⟨x,hx⟩ := cast
  refine ⟨c + d' + x,?_⟩
  intro L B bank rows hM
  let data : I := ⟨((L,B),bank),rows,hM⟩
  have hc (j) := (Classical.choose_spec (credits j) data).trans
    (show Classical.choose (credits j) ≤ c from
      Finset.le_sup (f := fun i : Fin d => Classical.choose (credits i)) (Finset.mem_univ j))
  have hd (j) := (Classical.choose_spec (debits j) data).trans
    (show Classical.choose (debits j) ≤ d' from
      Finset.le_sup (f := fun i : Fin d => Classical.choose (debits i)) (Finset.mem_univ j))
  exact ⟨fun j => (hc j).trans (by omega),fun j => (hd j).trans (by omega),(hx data).trans (by omega)⟩

def packetWorkCap (q d M U : ℕ) := Classical.choose (packet_work_exists q d M U)

theorem packet_work {q d U : ℕ} (L : Dispatch) (B : Repair q d) (bank : Bank) (rows : RowWork B U) :
    let K := packetWorkCap q d B.batch.maxWidth U
    (∀ i, ((enabledBatch L B).wire (B.wire i)).work ≤ K) ∧
    (∀ i, (RepairHistogram.debit (enabledBatch L B) i).work ≤ K) ∧
    (RepairHistogram.broadcastTerm (enabledBatch L B) bank).work ≤ K := by
  have bound := Classical.choose_spec (packet_work_exists q d B.batch.maxWidth U) L B bank rows rfl
  exact ⟨bound.credit,bound.debit,bound.broadcast⟩

end Hierarchy.ProtocolRAM.Calendar.StockCommit
end

end OAI
