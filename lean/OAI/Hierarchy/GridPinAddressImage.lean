import OAI.Hierarchy.GridOrderedPinOrigins
import OAI.Hierarchy.GridFactorPinSchedule

namespace OAI
/-! # The published physical pin number in the sparse wirer's encoding -/

namespace Hierarchy.GridPinAddressImage
open GridThrough GridThrough.Ordered FactorPinIntervals
noncomputable section
variable {r k n q d S N : ℕ}

def code : ((Cell k n×Fin q)×Fin d) ↪ Fin ((n+1)^k*(q*d)) where
  toFun x := dataCode (x.1.1,finProdFinEquiv (x.1.2,x.2))
  inj' := by
    rintro ⟨⟨c,t⟩,i⟩ ⟨⟨u,s⟩,j⟩ eqn
    obtain ⟨rfl,hit⟩ := Prod.mk.inj (dataCode.injective eqn)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (finProdFinEquiv.injective hit)
    rfl

theorem code_val (t : Cell k n×Fin q) (i : Fin d) :
    (code (t,i)).val=(GridTicks.index t).val*d+i.val := by
  simp [code,dataCode,GridTicks.index,finProdFinEquiv_apply_val]
  ring

variable (P : Layout (Cell k n×Fin q) S N d) (rail : Fin r↪Fin (S/2))
    (direction : Fin r→Fin k)
    (paired : ∀ e,P.origin (pairPorts rail (e,true))=P.origin (pairPorts rail (e,false)))

/-- The native destination bank needs the absolute address at the original
rail ordinal. The formula also applies to any injective relabelling of rails. -/
theorem address_at (e : Fin r) (b : Bool) :
    GridOrderedPinOrigins.slot (PinAssignment.ofFactorIntervals P direction (pairPorts rail) paired)
      (sides (e,b)).val = (code (P.address (pairPorts rail (e,b)))).val := by
  rw [GridOrderedPinOrigins.slot, dite_eq_left (sides (e,b)).isLt,GridOrderedPinOrigins.address_val,code_val]
  have same : P.tick (pairPorts rail (e,false))=P.tick (pairPorts rail (e,b)) := by
    cases b
    · rfl
    · exact congrArg P.owner (paired e).symm
  change (finFunctionFinEquiv (P.tick (pairPorts rail (e,false))).1).val*(q*d)+
    (P.tick (pairPorts rail (e,false))).2.val*d+(P.slot (pairPorts rail (e,b))).val =
    (GridTicks.index (P.tick (pairPorts rail (e,b)))).val*d+(P.slot (pairPorts rail (e,b))).val
  rw [same]
  simp [GridTicks.index,finProdFinEquiv_apply_val]
  ring

theorem literal_at (cell : Cell k n) (pin : Fin (q*d)) :
    let sc := finProdFinEquiv.symm pin
    (PinAssignment.ofFactorIntervals P direction (pairPorts rail) paired).literal (cell,pin) =
      P.literal (cell,sc.1) sc.2 := rfl

end
end Hierarchy.GridPinAddressImage

end OAI
