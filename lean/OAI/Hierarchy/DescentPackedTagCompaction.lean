import OAI.Hierarchy.DescentPackedLocalAtoms

namespace OAI
/-! A compacted numerical field is bounded by the original fields, including every padded output. -/
namespace Hierarchy.DescentPackedLocalAtoms
open DescentSIMDLookup
open scoped Classical
noncomputable section

theorem packed_field_bound {a n m bound : ℕ} (mask : Cell (1*n)) (value : Fin n→Cell a)
    (small : ∀i,(value i).val≤bound) (j : Fin m) :
    ((encode a m).symm (pack a n m mask (encode a n value)) j).val≤bound :=by
  simp only [pack,Equiv.symm_apply_apply,field]
  split
  · exact small _
  · simp

end
end Hierarchy.DescentPackedLocalAtoms

end OAI
