import OAI.Optimization.LinearProgramming.Geometry.LabelInputsUse
import OAI.Optimization.LinearProgramming.Geometry.BorderBatchInput

/-! The raw and relative initializer's concrete batch and projection preconditions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelInput

open RAM Matrix

variable {r s n : ℕ} {x : Buffers r s n} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}
  {price : Fin n → ℚ} {i : Fin n} {m : Memory ℚ}

/-- Prefix initialization writes values already specified by the initialized header. -/
theorem Header.border (h : Header x D E price i m) :
    BorderBatch.Inputs x.layout D price (geoCutoff n) m := by
  refine ⟨?_,h.precision,h.prices⟩
  obtain ⟨_,sc,sz,ds,ps,ts,rs,pv,hd,rw,cw,an,sp,mk,_,md⟩ := h.batch
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,(fun q => q.elim0),md⟩
  all_goals simp [PivotPrefixRAM.initial,sc,sz,ds,ps,ts,rs,pv,hd,rw,cw,an,sp,mk]

/-- All retained rounded entries precede the post-prefix allocation. -/
theorem Buffers.rounded_end_le_scratch (x : Buffers r s n) :
    x.layout.rounded+r*n ≤ x.layout.scratch :=
  x.layout.rounded_end.trans ((Nat.le_add_right _ _).trans x.layout.answers_end)

end LabelInput
end Geometry
end LinearProgramming
end Optimization
end OAI
