import OAI.Hierarchy.DescentOrdinaryNodeOrder
import OAI.Hierarchy.DescentTrunkBitHistory

namespace OAI
/-! # Actual retained scalar rows, cable relay rows, and bank nodes across a reset -/

namespace Hierarchy.DescentKernelHistory.NodeOrder
open Computability.BorderVNP.Crossing DescentSixParty DescentResetTrunks DescentRouterBank DescentNamedContact
open scoped Classical BigOperators
noncomputable section
variable {X Y P H Q : Type} [Fintype H] [Fintype Q] {n d L : ℕ} {bits : P→ℕ}
variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width)) (key : N.Edge↪Fin L)
variable (old : SiteBits (U:=X) N) (bank : SiteBits (U:=Y) R)
local notation "tr" => trunkBits N home group R key old bank
private def encode : Global tr → Global old ⊕ (N.Edge ⊕ Global bank)
  | ⟨.inl (false,h),⟨⟨u,atHome⟩,a⟩⟩ => by
    subst h
    exact .inl ⟨u,a⟩
  | ⟨.inl (true,_),e⟩=>.inr (.inl e.val)
  | ⟨.inr v,b⟩=>.inr (.inr ⟨v,b⟩)

private def decode : Global old ⊕ (N.Edge ⊕ Global bank) → Global tr
  | .inl ⟨u,a⟩=>⟨.inl (false,home u),⟨⟨u,rfl⟩,a⟩⟩
  | .inr (.inl e)=>⟨.inl (true,moved N home e),⟨e,rfl⟩⟩
  | .inr (.inr ⟨v,b⟩)=>⟨.inr v,b⟩

def trunkNames : Global tr ≃ Global old ⊕ (N.Edge ⊕ Global bank) where
  toFun := encode N home group R key old bank
  invFun := decode N home group R key old bank
  left_inv := by
    rintro ⟨⟨flag,h⟩|v,a⟩
    · cases flag
      · rcases a with ⟨⟨u,eqn⟩,a⟩
        cases eqn
        rfl
      · rcases a with ⟨e,eqn⟩
        cases eqn
        rfl
    · rfl
  right_inv := by rintro (⟨u,a⟩|e|⟨v,b⟩) <;> rfl

/-- Old and relay ranks are those actually issued by the previous stage. Bank rows
follow their local catalog order and selected physical host order. -/
def trunkOrdinal {a b c : ℕ} (prior : Global old≃Fin a) (relay : N.Edge≃Fin b)
    (op : Global bank≃Fin c) : Global tr ≃ Fin (a+(b+c)) :=
  (trunkNames N home group R key old bank).trans ((Equiv.sumCongr prior
    ((Equiv.sumCongr relay op).trans finSumFinEquiv)).trans finSumFinEquiv)

end
end Hierarchy.DescentKernelHistory.NodeOrder

end OAI
