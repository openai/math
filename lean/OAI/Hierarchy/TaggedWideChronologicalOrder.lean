import OAI.Hierarchy.ProbeSiteOrder
import OAI.Hierarchy.ProtocolRAMCatalogueOrdinal
import OAI.Hierarchy.TaggedWireRoleIndices
import OAI.Hierarchy.ProtocolRAMRepairCommodity
import OAI.Hierarchy.TaggedWireHistorySockets

namespace OAI
/-! # Original terminal ordinals in the native order of every chronological site state -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open AdaptiveProbe ReportSockets ProtocolRAM ProtocolRAM.Calendar.CatalogueRows
open scoped Classical

section Order

variable {A : Type} [Fintype A] {n : ℕ} (code : A ↪ Fin n)

def sortedRows : Fin (Fintype.card A) ≃ A := (SiteOrder.ofEmbedding code).name.symm

theorem sorted_key (i : Fin (Fintype.card A)) :
    code (sortedRows code i)=(SiteOrder.ofEmbedding code).ord i := by
  simpa [sortedRows] using ((SiteOrder.ofEmbedding code).reconstruct (sortedRows code i)).symm

theorem before_iff (i j : Fin (Fintype.card A)) :
    i<j ↔ code (sortedRows code i)<code (sortedRows code j) := by
  rw [sorted_key,sorted_key]
  exact (OrderEmbedding.lt_iff_lt _).symm

end Order

variable {h W k attempts : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : ReportSockets.Marks h W k attempts) (b : Board)
    (order : Fin b.coreRows ≃ Edges S h (2^W) k)
    (size : attempts*(ProtocolRAM.PurchaseFrozen.count h (2^W) k*ProtocolRAM.PurchaseFrozen.paths h S.degree depth)=b.boughtRows)
    {goods axes : ℕ} (g : Goods h W k ≃ Fin goods) (a : Catalysts h W k ≃ Fin axes)

def sparseKey : Source S π depth marked ↪ Fin (b.rows+(goods+axes)) :=
  ((b.ordinal S π depth marked order size).sumMap
    ((g.toEmbedding.sumMap a.toEmbedding).trans finSumFinEquiv.toEmbedding)).trans finSumFinEquiv.toEmbedding

theorem key_paid (e : Catalogue S π depth marked) :
    (sparseKey S π depth marked b order size g a (.inl e)).val=(b.ordinal S π depth marked order size e).val := rfl

theorem key_goods (i : Goods h W k) :
    (sparseKey S π depth marked b order size g a (.inr (.inl i))).val=b.rows+(g i).val := by
  simp [sparseKey,finSumFinEquiv,Fin.addCases,Function.Embedding.sumMap]

theorem key_reserve (i : Catalysts h W k) :
    (sparseKey S π depth marked b order size g a (.inr (.inr i))).val=b.rows+goods+(a i).val := by
  simp [sparseKey,finSumFinEquiv,Fin.addCases,Function.Embedding.sumMap,Nat.add_assoc]

def timeRows : Fin (Fintype.card (Source S π depth marked)) ≃ Source S π depth marked :=
  sortedRows (sparseKey S π depth marked b order size (PurchaseInventory.slotEquiv h (Stages h (2^W)) k) a)

theorem time_before (i j : Fin (Fintype.card (Source S π depth marked))) :
    let key := sparseKey S π depth marked b order size (PurchaseInventory.slotEquiv h (Stages h (2^W)) k) a
    let rows := timeRows S π depth marked b order size a
    i.val<j.val ↔ (key (rows i)).val<(key (rows j)).val := before_iff _ i j

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles

end
end OAI
