import OAI.Hierarchy.DescentResetRetainedPriorBanks

namespace OAI
/-! # Elimination of the two metadata and seven operand channels in the reset directory -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentOperandStateBanks
noncomputable section
variable (v : Layout)

theorem source_cases (P : Fin v.sources→Prop)
    (metadata : ∀(f : Fin 2) x,P (v.sourceID (if f=0 then v.occupiedField else v.arityField) x))
    (operand : ∀f arg x,P (v.sourceID (v.operandField f arg) x)) : ∀j,P j:=by
  intro j
  obtain ⟨⟨i,x⟩,rfl⟩:=(finProdFinEquiv : (Fin v.fields×Fin v.blocks)≃Fin v.sources).surjective j
  change P (v.sourceID i x)
  by_cases low:i.val<2
  · by_cases zero:i.val=0
    · have same:i=v.occupiedField:=Fin.ext zero
      simpa [same] using metadata (0 : Fin 2) x
    · have one:i.val=1:=by omega
      have same:i=v.arityField:=Fin.ext one
      simpa only [same,show (1:Fin 2)≠0 by decide,ite_false] using metadata 1 x
  · let pg:Pages v.previousArgs:=⟨i.val-2,by have up:=i.isLt;change _<2+7*v.previousArgs at up;omega⟩
    let pair:Fin 7×Fin v.previousArgs:=finProdFinEquiv.symm pg
    have eqn:finProdFinEquiv pair=pg:=finProdFinEquiv.apply_symm_apply pg
    have val:2+(finProdFinEquiv pair).val=i.val:=by rw [eqn];dsimp [pg];omega
    have eq_:v.operandField pair.1 pair.2=i:=Fin.ext val
    exact eq_ ▸ operand pair.1 pair.2 x

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
