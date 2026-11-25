import OAI.Hierarchy.DescentResetPublicOperandBook

namespace OAI
/-! Public tap operands start after all copies of the private back edge. -/
namespace Hierarchy.DescentRotorOperandQueryROM.Shape
open DescentSIMDLookup DescentPhysicalSplit DescentBatchedNodeOrder DescentRotor DescentLaneGates
open DescentDenseHostOrder DescentHostDirectory
open ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical
noncomputable section
variable {n h : ℕ} (G : NonlinearExpanders.Graph n h) (C : DescentRotorOperandQueryROM.Shape)
local notation "Q" => DescentCommonPalette.rotor G

theorem public_after_private (mult layers p node arg : ℕ) (actor : (Q).Site)
    (q : Mouth n) (hit : C.publicTap G mult layers p node arg actor=some q) :
    (C.flattened G mult layers p node actor)[arg]?=none :=by
  rcases actor with ⟨v,b|i⟩
  · simp [publicTap] at hit
  let order:=tapOrder layers C.batches (C.subrow G mult v) i
  by_cases live : node<Fintype.card (SpineRow (r:=layers) (m:=C.batches) (C.subrow G mult v) ⊕
      Block layers C.batches (C.subrow G mult v i))
  · have liveNum:=live
    simp at liveNum
    cases row:order.symm ⟨node,live⟩ with
    | inl s=>dsimp only [order] at row; simp [publicTap,liveNum,row] at hit
    | inr t=>
      dsimp only [order] at row
      cases socket:name (Physical.host G.arcs 0 0 0 0 0) v i with
      | inr e=>simp [publicTap,liveNum,row,socket] at hit
      | inl key=>
        rcases key with ⟨vertex,pin⟩
        let back:=C.spineReference G mult layers p v i true ⟨i,t⟩
        by_cases offset : back.count G C mult layers p≤arg
        · apply List.getElem?_eq_none
          simpa [flattened,privateRows,liveNum,row,socket,PrivateLane.names,back] using offset
        · dsimp only [back] at offset
          simp [publicTap,liveNum,row,socket,offset] at hit
  · have past:=live
    simp at past
    simp [publicTap,past] at hit

theorem selector_excludes_private (mult p split node arg : ℕ) (x : Fin 4→Cell C.fieldBits)
    (s : Bool) (root : DescentResetHostSize.Code C.residual) (req : Mouth n)
    (hit : C.public_selector G mult p node arg x=some (s,root,req)) (f : Fin 8) :
    C.flatReg G mult p split node arg f x=0:=by
  by_cases active : (x 1).val>0 ∧ (x 2).val%2=0
  · by_cases legal : (x 3).val<(roster G C.residual C.depth).card
    · let slot:=(DescentResetTrunkPalette.order G C.residual C.depth).symm ⟨(x 3).val,legal⟩
      cases shape:slot.val with
      | trunk t z=>dsimp only [slot] at shape; simp [public_selector,active,legal,shape] at hit
      | fall t z ds=>dsimp only [slot] at shape; simp [public_selector,active,legal,shape] at hit
      | good side label v=>
        have atSlot : ((DescentResetTrunkPalette.order G C.residual C.depth).symm ⟨(x 3).val,legal⟩).val
            = .good side label v:=shape
        by_cases allowed : ((x 1).val-1,label.2)∈codes C.residual
        · cases tap:C.publicTap G mult (DescentRecordedRotorLayers.layers n C.packet C.gain (x 0).val) p node arg v with
          | none=>simp [public_selector,active,legal,atSlot,allowed,tap] at hit
          | some q=>
            have no:=C.public_after_private G mult _ p node arg v q tap
            simp [flatReg,active.1,active.2,legal,atSlot,allowed,no]
        · simp [public_selector,active,legal,atSlot,allowed] at hit
    · simp [public_selector,active,legal] at hit
  · unfold public_selector at hit
    simp only [guard, ite_eq_right active, failure, Alternative.failure] at hit
    contradiction

end
end Hierarchy.DescentRotorOperandQueryROM.Shape

end OAI
