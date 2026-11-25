import OAI.Hierarchy.DescentBitDescription
import OAI.Hierarchy.DescentBitHistory
import OAI.Hierarchy.DescentOrderedResetTrunks

namespace OAI
/-! # Which actual incident bits the reset feeds to old gates and router gates -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentResetAttachments DescentResetTrunks DescentNamedContact DescentRouterBank
open scoped Classical BigOperators
noncomputable section
variable {d n : ℕ} {P H Q : Type} [Fintype H] [Fintype Q] {bits : P→ℕ}
variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width))
local notation "M" => DescentResetTrunks.network N home group R

variable {L : ℕ} (key : N.Edge↪Fin L)

/-- On the old gate, outgoing and exterior bits are unchanged. Each incoming
bit is taken from its precise coordinate in the coalesced lower trunk. -/
def trunkOldBit (v : N.Site) : BitRef (boundaryWidth N v)→
    BitRef (boundaryWidth (M) (.inl (false,home v)))
  | ⟨.inr p,j⟩=>⟨.inr ⟨p.val,congrArg (fun x=>Sum.inl (false,home x)) p.property⟩,j⟩
  | ⟨.inl e,j⟩=>
    if left : N.src e.val=v then
      ⟨.inl ⟨.inl (false,e.val),Or.inl (congrArg (fun x=>Sum.inl (false,home x)) left)⟩,j⟩
    else
      let right := e.property.resolve_left left
      let cable : Fibre (moved N home) (home v) := ⟨e.val,congrArg home right⟩
      ⟨.inl ⟨.inr (.inl (home v)),Or.inl rfl⟩,
        DescentOrderedWords.address (DescentOrderedReset.fibreKey key (moved N home) (home v)) (fun i : Fibre (moved N home) (home v)=>N.width i.val) ⟨cable,j⟩⟩

omit [Fintype Q] in
theorem trunkOldBit_read (a : (M).Assignment) (pins : Ports bits) (v : N.Site) (b : BitRef (boundaryWidth N v)) :
    boundaryRead (M) a pins (.inl (false,home v)) (trunkOldBit N home group R key v b).1 (trunkOldBit N home group R key v b).2=
      boundaryRead N (oldRows N (DescentResetTrunks.Ordered.original N home group R key a) v) pins v b.1 b.2 := by
  rcases b with ⟨⟨e,incident⟩|p,j⟩
  · change bitInput (M) a pins (.inl (false,home v))
        (trunkOldBit N home group R key v ⟨.inl ⟨e,incident⟩,j⟩) =
      DescentResetTrunks.Ordered.original N home group R key a (side N v e) e j
    by_cases left : N.src e=v
    · have selected : side N v e=false := by simp [side,left]
      simp only [trunkOldBit,dite_eq_left left,selected]; rfl
    · have right : N.dst e=v := incident.resolve_left left
      subst v
      have selected : side N (N.dst e) e=true := by simp [side,left]
      simp only [trunkOldBit,dite_eq_right left,selected]; rfl
  · rfl

/-- Each old router port carries the bundle at the given (side,group).
Decomposing its bit index identifies one actual stem and its bit offset. -/
def trunkBankBit (v : R.Site) : BitRef (boundaryWidth R v)→
    BitRef (boundaryWidth (M) (.inr v))
  | ⟨.inl e,j⟩=>⟨.inl ⟨.inr (.inr e.val),e.property.imp (congrArg Sum.inr) (congrArg Sum.inr)⟩,j⟩
  | ⟨.inr p,j⟩=>
    let s:=p.val.1
    let q:=p.val.2
    let w:=fun e : Fibre (group s) q=>N.width e.val
    let item := (DescentOrderedWords.address (DescentOrderedReset.fibreKey key (group s) q) w).symm j
    let e:=item.1.val
    have atGate : R.attach (s,group s e)=v := by
      rw [show group s e=q from item.1.property]
      exact p.property
    ⟨.inl ⟨.inl (s,e),Or.inr (congrArg Sum.inr atGate)⟩,item.2⟩

omit [Fintype Q] in
theorem trunkBankBit_read (a : (M).Assignment) (pins : Ports bits) (v : R.Site) (b : BitRef (boundaryWidth R v)) :
    boundaryRead (M) a pins (.inr v) (trunkBankBit N home group R key v b).1 (trunkBankBit N home group R key v b).2=
      boundaryRead R (DescentResetTrunks.Ordered.decode N home group R key a).2.2
        (DescentResetTrunks.Ordered.public N group key (DescentResetTrunks.Ordered.decode N home group R key a).1) v b.1 b.2 := by
  rcases b with ⟨e|p,j⟩
  · rfl
  · rfl

end
end Hierarchy.DescentKernelHistory

end OAI
