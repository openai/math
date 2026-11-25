import OAI.Hierarchy.GridPinScanPrefix

namespace OAI
/-! # The native class-major receiver filter returns the selected factors in order -/

namespace Hierarchy.GridReceiverDirectoryOrder
open GridPinPrefixMemory FactorAllocation
variable {N d T : ℕ}

noncomputable def row (ht : 0<T) (w : ℕ) (cost : Fin N→Fin d→ℕ) (target : Fin T) (i : ℕ) : Option (Fin N) :=
  (classRow (factorKey w cost) i).bind fun f => if owner ht w cost f=target then some f else none

theorem row_at (ht : 0<T) (w : ℕ) (cost : Fin N→Fin d→ℕ) (target : Fin T)
    (i : ℕ) (f : Fin N) (hf : i%N=f.val) :
    row ht w cost target i = if factorKey w cost f=i/N ∧ owner ht w cost f=target then some f else none := by
  have hi : i%N<N := hf.trans_lt f.isLt
  have eq : (⟨i%N,hi⟩ : Fin N)=f := Fin.ext hf
  simp only [row,classRow,dite_eq_left hi,eq]
  by_cases key : factorKey w cost f=i/N <;> by_cases owns : owner ht w cost f=target <;>
    simp [Option.guard,key,owns]

theorem rows (ht : 0<T) (w : ℕ) (cost : Fin N→Fin d→ℕ) (target : Fin T) :
    (List.range (((20*(w+1)+2)^d)*N)).filterMap (row ht w cost target) =
      factors w cost (List.finRange N) target := by
  rw [←classStream_at ht w cost target,←factor_ordinals w cost,List.filter_filterMap]
  apply List.filterMap_congr
  intro i _
  unfold row
  cases classRow (factorKey w cost) i with
  | none => rfl
  | some f => by_cases h : owner ht w cost f=target <;> simp [h,Option.filter]

end Hierarchy.GridReceiverDirectoryOrder

end OAI
