import OAI.Optimization.LinearProgramming.Geometry.LabelBuffers
import OAI.Optimization.LinearProgramming.Geometry.PivotPrefixMemory
import OAI.Optimization.LinearProgramming.Geometry.PostPivotLayout

/-! Relocatable labels feed both stages of the executable geometric oracle. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelInput

open RAM BorderBatch Matrix
variable {K : Type} {r s n : ℕ}

/-- The same initialized header supplies the prefix and post-prefix rational routines. -/
theorem Header.prefix {x : Buffers r s n} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}
    {price : Fin n → ℚ} {i : Fin n} {m : Memory ℚ} (h : Header x D E price i m) :
    PivotPrefixRAM.Layout m r n (geoCutoff n) := by
  have h1 := x.dualHigh; have h2 := x.dualEnd; have h3 := x.primalEnd; have h4 := x.priceEnd
  refine ⟨h.batch.height,h.batch.width,h.precision,?_,?_,?_,?_⟩
  · rw [h.batch.tripleAddr]; change 256 ≤ x.free; omega
  · rw [h.batch.roundedAddr]; change 256 ≤ x.free+3*n; omega
  · rw [h.batch.pivotAddr]; exact x.indicesHigh
  · rw [h.batch.tripleAddr,h.batch.roundedAddr]; exact Or.inl le_rfl

theorem Header.post {x : Buffers r s n} {D : Matrix (Fin r) (Fin n) K} {E : Matrix (Fin s) (Fin n) K}
    {price : Fin n → K} {i : Fin n} {m : Memory K} (h : Header x D E price i m) :
    PostPivotLayout.Inputs r x.layout.rounded x.layout.scratch i m :=
  ⟨h.batch.height,h.batch.width,h.batch.roundedAddr,h.index,h.afterPivotFree⟩

end LabelInput
end Geometry
end LinearProgramming
end Optimization
end OAI
