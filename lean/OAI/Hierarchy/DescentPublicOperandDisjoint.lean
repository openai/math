import OAI.Hierarchy.DescentRotorArgumentDisjoint

namespace OAI
/-! A public tap or a fallback tree input cannot select a private rotor input at the same argument. -/
namespace Hierarchy.DescentResetPublicOperandBook.Config
open DescentSIMDLookup DescentDenseHostOrder DescentFallbackOperandBranch DescentHostDirectory
noncomputable section
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h) (C : DescentResetPublicOperandBook.Config)

/-- All seven private correction fields and its source query vanish when the public
interpreter produces any (slot,ticket,multiplicity,mark) at this node and argument. -/
theorem mixed_excludes_private (node arg split : ℕ) (x : C.Data n) (out : ℕ×ℕ×ℕ×Bool)
    (found : C.mixed board node arg x=some out) (field : Fin 8) :
    C.rotor.flatReg board C.multiplicity C.grain split node arg field (C.reg x)=0:=by
  let regs:=C.reg x
  by_cases occupied : (C.oldConfig.header (C.basic x) 0).val=0
  · simp [mixed,occupied] at found
  cases publicSel:C.rotor.public_selector board C.multiplicity C.grain node arg regs with
  | some p=>
    rcases p with ⟨side,key,pin⟩
    exact C.rotor.selector_excludes_private board C.multiplicity C.grain split node arg regs side key pin publicSel field
  | none=>
    have fall : C.oldConfig.mixed board node arg (C.basic x)=some out:=by
      simpa only [mixed,ite_eq_right occupied,←show regs=C.reg x by rfl,publicSel] using found
    change C.rotor.flatReg board C.multiplicity C.grain split node arg field regs=0
    by_cases okay : (regs 1).val>0 ∧ (regs 2).val%2=0 ∧ (regs 3).val<(roster board C.residual C.maxDepth).card
    · let raw:=(DescentResetTrunkPalette.order board C.residual C.maxDepth).symm ⟨(regs 3).val,okay.2.2⟩
      cases shape:raw.val with
      | trunk side z=>
        dsimp only [raw] at shape
        unfold DescentRotorOperandQueryROM.Shape.flatReg
        split
        · split <;> first | rfl | rename_i eqn; exact nomatch eqn.symm.trans shape
        · rfl
      | fall side z ds=>
        dsimp only [raw] at shape
        unfold DescentRotorOperandQueryROM.Shape.flatReg
        split
        · split <;> first | rfl | rename_i eqn; exact nomatch eqn.symm.trans shape
        · rfl
      | good side z site=>
        have h : (C.oldConfig.header (C.basic x) 2).val<(roster board C.residual C.maxDepth).card:=okay.2.2
        have value : ((DescentResetTrunkPalette.order board C.residual C.maxDepth).symm
            ⟨(C.oldConfig.header (C.basic x) 2).val,h⟩).val=.good side z site:=shape
        simp [DescentFallbackOperandBranch.Config.mixed,occupied,h,value] at fall
    · unfold DescentRotorOperandQueryROM.Shape.flatReg
      split
      · rename_i active
        exact (okay active).elim
      · rfl

theorem disjoint_at (b : ℕ) (field : Option (Fin 7)) (index : Fin C.oldConfig.mouths)
    (x : C.Data n) (i : Fin 8) (split : ℕ) :
    C.column board b field index x=0 ∨
      C.rotor.flatReg board C.multiplicity C.grain split
        (finProdFinEquiv.symm index : Fin C.args×Fin C.nodes).2.val
        (finProdFinEquiv.symm index : Fin C.args×Fin C.nodes).1.val i (C.reg x)=0:=by
  let j:Fin C.args×Fin C.nodes:=finProdFinEquiv.symm index
  cases hit:C.mixed board j.2.val j.1.val x with
  | none=>left;simp only [column,←show j=finProdFinEquiv.symm index by rfl,hit]
  | some out=>right;exact C.mixed_excludes_private board j.2.val j.1.val split x out hit i

end
end Hierarchy.DescentResetPublicOperandBook.Config

end OAI
