import OAI.Hierarchy.DescentAlignedOrderedWords
import OAI.Hierarchy.DescentTrunkBitRefs
import OAI.Hierarchy.DescentBitDescription
import OAI.Hierarchy.DescentBitHistory
import OAI.Hierarchy.DescentOrderedResetTrunks

namespace OAI
/-! # Aligned whole-word references of the actual chronological reset trunks -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentResetAttachments DescentResetTrunks DescentNamedContact DescentRouterBank
open scoped Classical BigOperators
noncomputable section
variable {d n : ℕ} {P H Q : Type} [Fintype H] [Fintype Q] {bits : P→ℕ}
variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width))
local notation "M" => DescentResetTrunks.network N home group R

variable {L : ℕ} (key : N.Edge↪Fin L)

open DescentOrderedWords
variable {p : ℕ} (whole : ∀e,p∣N.width e)

include whole in
omit [Fintype Q] in
/-- Exterior and outgoing ports preserve the block number; an incoming block
uses the chronological prefix of its old cable, which is itself p-aligned. -/
theorem trunkOldBit_aligned (v : N.Site) (q : Boundary N v)
    (z : Aligned p (boundaryWidth N v q)) :
    ∃t : Boundary (M) (.inl (false,home v)),∃y : Aligned p (boundaryWidth (M) _ t),
      ∀d,trunkOldBit N home group R key v ⟨q,z.bit d⟩=⟨t,y.bit d⟩ := by
  rcases q with e|h
  · by_cases left : N.src e.val=v
    · refine ⟨.inl ⟨.inl (false,e.val),Or.inl (congrArg (fun x=>Sum.inl (false,home x)) left)⟩,z,?_⟩
      intro d
      simp only [trunkOldBit,dite_eq_left left]; rfl
    · let cable : Fibre (moved N home) (home v) := ⟨e.val,congrArg home (e.property.resolve_left left)⟩
      let rank:=DescentOrderedReset.fibreKey key (moved N home) (home v)
      let w:=fun i : Fibre (moved N home) (home v)=>N.width i.val
      let y:=inside rank w (fun i=>whole i.val) cable z
      refine ⟨.inl ⟨.inr (.inl (home v)),Or.inl rfl⟩,y,?_⟩
      intro d
      simp only [trunkOldBit,dite_eq_right left]
      exact congrArg (Sigma.mk _) (inside_read rank w (fun i=>whole i.val) cable z d).symm
  · exact ⟨.inr ⟨h.val,congrArg (fun x=>Sum.inl (false,home x)) h.property⟩,z,fun _=>rfl⟩

include whole in
omit [Fintype Q] in
/-- Even at a public router word, the inverse prefix scan on its first digit
selects the old cable for every digit of this aligned block. -/
theorem trunkBankBit_aligned (hp : 0<p) (v : R.Site) (q : Boundary R v)
    (z : Aligned p (boundaryWidth R v q)) :
    ∃t : Boundary (M) (.inr v),∃y : Aligned p (boundaryWidth (M) _ t),
      ∀d,trunkBankBit N home group R key v ⟨q,z.bit d⟩=⟨t,y.bit d⟩ := by
  rcases q with e|q
  · exact ⟨.inl ⟨.inr (.inr e.val),e.property.imp (congrArg Sum.inr) (congrArg Sum.inr)⟩,z,fun _=>rfl⟩
  · let rank:=DescentOrderedReset.fibreKey key (group q.val.1) q.val.2
    let w:=fun i : Fibre (group q.val.1) q.val.2=>N.width i.val
    obtain ⟨e,y,read⟩:=outside rank w (fun i=>whole i.val) hp z
    let port (t : Σ i : Fibre (group q.val.1) q.val.2,Fin (N.width i.val)) :
        BitRef (boundaryWidth (M) (.inr v)) :=
      ⟨.inl ⟨.inl (q.val.1,t.1.val),Or.inr (congrArg Sum.inr (show R.attach (q.val.1,group q.val.1 t.1.val)=v by
        rw [t.1.property];exact q.property))⟩,t.2⟩
    refine ⟨.inl ⟨.inl (q.val.1,e.val),Or.inr (congrArg Sum.inr (show R.attach (q.val.1,group q.val.1 e.val)=v by
      rw [e.property];exact q.property))⟩,y,fun d=>?_⟩
    exact congrArg port (read d)

end
end Hierarchy.DescentKernelHistory

end OAI
