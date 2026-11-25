import OAI.Hierarchy.DescentRotorFlatFields
import OAI.Hierarchy.DescentResetPublicOperandBook
import OAI.Hierarchy.DescentPhysicalOperandLaws

namespace OAI
/-! # A retained trunk contributes neither a rotor nor an exceptional-branch operand -/
namespace Hierarchy
open DescentSIMDLookup DescentDenseHostOrder DescentResetTrunkPalette
open scoped Classical Fin.CommRing
noncomputable section
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h)

namespace DescentRotorOperandQueryROM.Shape
variable (C : DescentRotorOperandQueryROM.Shape) (x : Fin 4→Cell C.fieldBits)
    (shape : ↥(roster board C.residual C.depth))
    (seen : (x 3).val=(localRank board C.residual C.depth shape).val)
    (primary : ∃key,shape.val=.trunk false key)

include seen primary in
theorem flat_primary (mult grain split node arg : ℕ) (f : Fin 8) :
    C.flatReg board mult grain split node arg f x=0 := by
  obtain ⟨key,trunk⟩:=primary
  unfold flatReg
  split
  · rename_i active
    have ix : (⟨(x 3).val,active.2.2⟩:Fin (roster board C.residual C.depth).card)=
        DescentResetTrunkPalette.order board C.residual C.depth shape:=Fin.ext seen
    simp only [ix,Equiv.symm_apply_apply,trunk]
  · rfl

include seen in
theorem flat_fallback (side peer path) (fallback : shape.val=.fall side peer path)
    (mult grain split node arg : ℕ) (f : Fin 8) : C.flatReg board mult grain split node arg f x=0 := by
  unfold flatReg
  split
  · rename_i active
    have ix : (⟨(x 3).val,active.2.2⟩:Fin (roster board C.residual C.depth).card)=
        DescentResetTrunkPalette.order board C.residual C.depth shape:=Fin.ext seen
    simp only [ix,Equiv.symm_apply_apply,fallback]
  · rfl


include seen primary in
theorem selector_primary (mult grain node arg : ℕ) :
    C.public_selector board mult grain node arg x=none := by
  obtain ⟨key,trunk⟩:=primary
  have bound : (x 3).val<(roster board C.residual C.depth).card:=seen ▸ (localRank _ _ _ shape).isLt
  have ix : (⟨(x 3).val,bound⟩:Fin (roster board C.residual C.depth).card)=
    DescentResetTrunkPalette.order board C.residual C.depth shape:=Fin.ext seen
  by_cases active : 0<(x 1).val ∧ (x 2).val%2=0 <;>simp [public_selector,active,bound,ix,trunk]

end DescentRotorOperandQueryROM.Shape

namespace DescentFallbackOperandBranch.Config
variable (C : DescentFallbackOperandBranch.Config)
theorem tree_primary (x : C.Data n) (shape : ↥(roster board C.residual C.maxDepth))
    (seen : (C.header x 2).val=(localRank board C.residual C.maxDepth shape).val)
    (primary : ∃key,shape.val=.trunk false key) (node arg : ℕ) : C.mixed board node arg x=none := by
  obtain ⟨key,trunk⟩:=primary
  have bound : (C.header x 2).val<(roster board C.residual C.maxDepth).card:=seen ▸ (localRank _ _ _ shape).isLt
  have ix : (⟨(C.header x 2).val,bound⟩:Fin (roster board C.residual C.maxDepth).card)=
    DescentResetTrunkPalette.order board C.residual C.maxDepth shape:=Fin.ext seen
  by_cases blank : (C.header x 0).val=0 <;>simp only [mixed,blank,ite_true,ite_false,dite_eq_left bound,ix,Equiv.symm_apply_apply,trunk]

end DescentFallbackOperandBranch.Config
namespace DescentResetPublicOperandBook.Config
variable (C : DescentResetPublicOperandBook.Config)
theorem primary_column (x : C.Data n) (shape : ↥(roster board C.residual C.maxDepth))
    (seen : (C.oldConfig.header (C.basic x) 2).val=(localRank board C.residual C.maxDepth shape).val)
    (primary : ∃key,shape.val=.trunk false key) (width : ℕ) (f : Option (Fin 7)) (i : Fin C.oldConfig.mouths) :
    C.column board width f i x=0 := by
  let q : Fin C.args × Fin C.nodes:=finProdFinEquiv.symm i
  have tap:=C.rotor.selector_primary board (C.reg x) shape seen primary C.multiplicity C.grain q.2.val q.1.val
  have tree:=C.oldConfig.tree_primary board (C.basic x) shape seen primary q.2.val q.1.val
  have empty_ : C.mixed board q.2.val q.1.val x=none:=by
    unfold mixed
    split <;> simp only [tap,tree]
  dsimp only [q] at empty_
  simp only [column,empty_]

end DescentResetPublicOperandBook.Config
end
end Hierarchy

end OAI
