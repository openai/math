import OAI.ThreeFlat.RAM.TraceBucketFields

namespace OAI
/-! # Word-width bounds for each native four-word field selection -/

namespace ThreeFlat.RAM.TraceBucketFields
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr

/-- Original-cell lookup reads one dictionary entry and one of the
common polynomial-size table-ID entries. The other multiplications are
ordinary modular register operations. -/
theorem original_fits {W : ℕ} (data : Param→ℕ) (m : ℕ→ℕ) (v : Fin 13→ℕ)
    (small : ∀ i, v i < 2^W) (word : 3<2^W)
    (dict : v 11+(v 2 ^^^ v 3)<2^W) (ids : v 12+v 5<2^W) :
    original.Fits W data m v := by
  have deltaBound : v 2 ^^^ v 3 < 2^W := by omega
  have quotBound : (v 2 ^^^ v 3)/v 10<2^W := (Nat.div_le_self ..).trans_lt deltaBound
  have two : 2<2^W := by omega
  by_cases field : v 0<3 <;> by_cases lit : v 1<2 <;>
    simp [original,delta,reserve,Formula.Fits,Formula.natural,opFits,natOp,natTest,
      small,word,two,dict,ids,field,lit,deltaBound,quotBound]

theorem compare_fits {W : ℕ} (data : Param→ℕ) (m : ℕ→ℕ) (v : Fin 15→ℕ)
    (small : ∀ i, v i<2^W) (word : 3<2^W) (header : 2+v 6<2^W) (depth : v 5+1<2^W) :
    compare.Fits W data m v := by
  have one : 1<2^W := by omega
  have two : 2<2^W := by omega
  have zero : 0 < 2^W := by omega
  simp [compare,emit,Formula.Fits,Formula.natural,opFits,natOp,natTest,small,zero,one,two,header,depth]
 ; split_ifs <;> simp_all

theorem hole_fits {W : ℕ} (data : Param→ℕ) (m : ℕ→ℕ) (v : Fin 7→ℕ)
    (field : v 0<2^W) (valid : v 4<2^W) (word : 3<2^W) : hole.Fits W data m v := by
  have zero : 0 < 2^W := by omega
  simp [hole,Formula.Fits,Formula.natural,opFits,natTest,field,valid,word,zero]
 ; split_ifs <;> simp_all

end ThreeFlat.RAM.TraceBucketFields

end OAI
