import OAI.Hierarchy.DescentFreshRoleHeaderData
import OAI.Hierarchy.DescentTerminalSliceRuns

namespace OAI
/-! # The fresh role exposes one whole word per original operand -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentTerminalSliceRuns DescentBundleHistory DescentSixParty
noncomputable section
variable {F : Type} [Field F]

private theorem repeated_whole (q : ℕ) :
    repeatFields (List.replicate q whole)=List.replicate q whole:=by
  induction q with
  | zero => rfl
  | succ q ih => simp only [List.replicate_succ,repeatFields,List.flatMap_cons] at ih ⊢
                 simpa [whole] using congrArg (List.cons whole) ih

theorem fresh_occurrences (G : PoweredGadget F) (p z : ℕ) (profile : Profile G.C) (party : Fin 6) :
    repeatFields (DescentFreshRoleFields.header G p z profile party).flatten=
      List.replicate (DescentFreshRoleFields.arity G p z profile party) whole:=by
  let rows:=DescentFreshRoleFields.header G p z profile party
  have uniform : rows.flatten=List.replicate rows.flatten.length whole:=by
    apply List.eq_replicate_length.mpr
    intro v hv
    obtain ⟨row,inRows,atRow⟩:=List.mem_flatten.mp hv
    obtain ⟨idx,rfl⟩:=List.mem_ofFn.mp inRows
    exact (List.mem_replicate.mp atRow).2
  have count : rows.flatten.length=DescentFreshRoleFields.arity G p z profile party:=by
    simp only [rows,DescentFreshRoleFields.header,DescentFreshRoleFields.arity,
      List.length_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_apply,List.length_replicate]
  change repeatFields rows.flatten=_
  rw [uniform,count,repeated_whole]

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
