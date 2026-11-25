import OAI.ThreeFlat.Diagonal.TraceSuffixPins
import OAI.ThreeFlat.RAM.HistoryCompiledRows

namespace OAI
/-! # The original table IDs are retained by public pin specialization -/

namespace ThreeFlat.Diagonal.TraceSuffix
open RAM.BitLayout RAM.HistoryCompiledRows
variable {F : Type*} {old free ports : ℕ}

theorem metadata_eq (N : BitNetwork F (old+ports)) (clip : free≤old) (start : ℕ)
    (pub : ℕ→Bool) (tag : ((Fin 3→Bool)→F)→ℕ) (i : Fin N.cells) (j : Fin 4) :
    metadata tag (network N clip start pub) i j=field old free start pub j.val (metadata tag N i j) := by
  by_cases h : j.val<3
  · simp only [metadata,field,h,dite_true,ite_true]
    exact source_address clip start pub _
  · simp [metadata,field,h,network]


end ThreeFlat.Diagonal.TraceSuffix

end OAI
