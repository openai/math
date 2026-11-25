import OAI.Hierarchy.ProtocolRAMCommittedTape
import OAI.Hierarchy.ProtocolRAMFailurePadding

namespace OAI
/-! # Counting committed histogram rows from the live discrepancy pass -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM PurchaseStage RepairHistogram
open scoped BigOperators Fin.CommRing Classical
noncomputable section
variable {w q d digits : ℕ}

/-- At a chosen failed row the native decision and the budgeted stock are all
read earlier than the generated histogram. Padding is included in the mass
and validation test. -/
theorem mask_committed (L : Dispatch) (B : Repair q d) (m : Memory w) (j : Fin L.candidates)
    (wide : 4≤2^w) (room : L.candidates≤2^w) (padded : L.candidates≤B.repairBits.size)
    (mode : AttemptGate.actual B.policy (B.tests.after m)=2)
    (failure : B.failedMIS.read (B.tests.after m) (B.batch.owner.eval (B.tests.after m) (j.val:Word w))≠0)
    (packet : B.batch.packet.eval (postSnapshot L B m) (j.val:Word w)≠0)
    (funded : ∀ i,((B.batch.need i).eval (postSnapshot L B m) (j.val:Word w)).val≤
      ((B.batch.stock i).eval (postSnapshot L B m) (j.val:Word w)).val)
    (valid : (enabledBatch L B).withinPacket (postSnapshot L B m) (j.val:Word w))
    (mass : (∑ t,(((enabledBatch L B).field t).eval (postSnapshot L B m) (j.val:Word w)).val)=(enabledBatch L B).copies) :
    committed (enabledBatch L B) (postSnapshot L B m) (j.val:Word w) :=
  ⟨(post_selected L B m j wide room padded).2 ⟨⟨mode,failure⟩,packet,funded⟩,valid,mass⟩

/-- A joint real/dummy discrepancy test is compared against the requested
site population, with its failing strip mapped into an actual committed row.
The density constant depends only on the price box and fixed resolution. -/
theorem density (s : StripTest digits) (source : Memory w) (actual : Fin s.rows→ℝ)
    (b : Batch q d) (m : Memory w) (target : ℕ) (entry : Fin s.rows ↪ Fin target)
    (C ρ : ℝ) (εpos : 0<s.tolerance) (precise : 0<s.precision) (boxPos : 0≤C)
    (rate : ρ*C≤2*s.tolerance) (strict : 0<C) (wide : 0<w) (fit : s.failure.cut<2^w)
    (population : (s.liveRows source).card≤ s.population) (dummy : ∀ i∉s.liveRows source,actual i=0)
    (box : ∀ i,(s.failure.value source i:ℝ)/s.precision≤C)
    (near : ∀ i∈s.liveRows source,|(s.failure.value source i:ℝ)/s.precision-actual i|≤ s.tolerance)
    (trigger : s.failure.globalBound≤∑ i,s.failure.value source i)
    (selected : ∀ i∈s.failedRows source,i∈s.liveRows source → s.tolerance<actual i →
      committed b m ((entry i).val:Word w)) :
    ρ*s.population≤(liveRows b m target).card := by
  obtain ⟨count,large⟩ := (s.padded source actual εpos precise boxPos wide fit population dummy box near).1 trigger
  have inc : (s.failedRows source).map entry ⊆ liveRows b m target := by
    intro e he
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,selected j hj (large j hj).1 (large j hj).2⟩
  have card : (s.failedRows source).card≤(liveRows b m target).card := by simpa using Finset.card_le_card inc
  have part : ρ*s.population≤(s.failedRows source).card := by
    apply (le_of_mul_le_mul_right _ strict)
    calc
      (ρ*s.population)*C = (ρ*C)*s.population := by ring
      _ ≤ (2*s.tolerance)*s.population := mul_le_mul_of_nonneg_right rate (Nat.cast_nonneg _)
      _ ≤ _ := count
  exact part.trans (Nat.cast_le.mpr card)

end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
