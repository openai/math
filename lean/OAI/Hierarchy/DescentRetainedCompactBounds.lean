import OAI.Hierarchy.DescentResetRetainedPlacement

namespace OAI
namespace Hierarchy.DescentRetainedTargetPlacement.Chart
open DescentResetRetainedPlacement DescentSIMDLookup DescentPackedZip
open scoped Fin.CommRing Classical
noncomputable section

section
variable {U : ℕ} (v : DescentResetRetainedPlacement.Chart) (b : Batch)

def selected (keep : Fin v.shapes→Bool) (Y : Fin v.shapes→Fin v.oldHosts→Fin v.groups→Cell b.bits)
    (h : Fin v.sparse) (g : Fin v.groups) : Cell b.bits :=
  if keep (v.shape h) then Y (v.shape h) (v.previous h) g else 0

def compact (keep : Fin v.shapes→Bool) (name : Fin U→Fin v.sparse)
    (Y : Fin (b.fields*v.shapes)→Fin v.oldHosts→Fin (v.groups*v.blocks)→Cell b.bits) (i : Fin b.fields) (x : Fin v.blocks) :=
  DescentResetDenseOperand.dense (H:=v.newHosts) name
    (selected v b keep (fun t h g=>Y (finProdFinEquiv (i,t)) h (finProdFinEquiv (g,x))))

end

/-- Compaction and the empty destinations preserve a common bound on a chosen physical column. -/
theorem compact_le (v : DescentResetRetainedPlacement.Chart) (b : Batch) {U : ℕ}
    (keep : Fin v.shapes→Bool) (name : Fin U→Fin v.sparse)
    (Y : Fin (b.fields*v.shapes)→Fin v.oldHosts→Fin (v.groups*v.blocks)→Cell b.bits)
    (i : Fin b.fields) (bound : ℕ)
    (valid : ∀t h g, (Y (finProdFinEquiv (i,t)) h g).val≤bound)
    (x : Fin v.blocks) (h : Fin v.newHosts) (g : Fin v.groups) :
    (compact v b keep name Y i x h g).val≤bound :=by
  by_cases used : h.val<U
  · let donor:=name ⟨h.val,used⟩
    by_cases active : keep (v.shape donor)=true
    · simpa [compact,DescentResetDenseOperand.dense,selected,used,donor,active,
        show keep (v.shape (name ⟨h.val,used⟩))=true from active] using
        valid (v.shape donor) (v.previous donor) (finProdFinEquiv (g,x))
    · simp [compact,DescentResetDenseOperand.dense,selected,used,
        show ¬keep (v.shape (name ⟨h.val,used⟩))=true from active]
  · simp [compact,DescentResetDenseOperand.dense,used]

end
end Hierarchy.DescentRetainedTargetPlacement.Chart

end OAI
