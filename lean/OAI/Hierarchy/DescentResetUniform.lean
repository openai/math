import OAI.Hierarchy.DescentResetReadout

namespace OAI
/-! # Installing a measured finite router on literal uniform cable occurrences -/

namespace Hierarchy.DescentResetAttachments
open DescentRouterBank DescentSixParty Computability.BorderVNP.Crossing DescentResetInvoice
open scoped BigOperators Classical
noncomputable section

variable {F : Type} [Field F] {Q : Type} [Fintype Q] {P : Type} {bits : P→ℕ}
variable {d n : ℕ} (A : MarkedWorld F n P bits) (hub : A.graph.Site→Bool)
variable (group : Bool→A.graph.Edge→Q)

/-- The installed graph can be read without choosing a witness from an existential. -/
def mount {w : A.graph.Edge→ℕ} (eqn : w=A.graph.width)
    (B : Network d (Bool×Q) (publicWidth group w)) (T : B.Tables F) : MarkedWorld F d P bits := by
  subst w
  exact resetWorld A group B T hub

def mountHub {w : A.graph.Edge→ℕ} (eqn : w=A.graph.width)
    (B : Network d (Bool×Q) (publicWidth group w)) (T : B.Tables F) :
    (mount A hub group eqn B T).graph.Site→Bool := by
  subst w
  exact nextHub A group B hub

omit [Fintype Q] in
theorem install {w : A.graph.Edge→ℕ} (eqn : w=A.graph.width)
    (B : Network d (Bool×Q) (publicWidth group w)) (T : B.Tables F)
    (exactBank : ∀p,B.value T p=if publicRows group w p false=publicRows group w p true then 1 else 0)
    (ordinary : ∀e∈A.core,hub (A.graph.src e)=false ∧ hub (A.graph.dst e)=false)
    (tether : ∀e∉A.core,hub (A.graph.src e)≠hub (A.graph.dst e))
    (price ε : ℝ) (hp : 0≤price) (he : 0≤ε) (h C β Ht : ℕ)
    (measured : price*((∑e,B.width e:ℕ):ℝ) ≤ internalRate h C*(price*A.liveWidth+ε)+
      exteriorRate h C β Ht*(price*A.tetherWidth)) :
    let W := mount A hub group eqn B T
    let next := mountHub A hub group eqn B T
    (∀p,W.value p=A.value p) ∧ W.tetherWidth=A.tetherWidth ∧
      (∀e∈W.core,next (W.graph.src e)=false ∧ next (W.graph.dst e)=false) ∧
      (∀e∉W.core,next (W.graph.src e)≠next (W.graph.dst e)) ∧
      price*W.liveWidth≤splicedRate h C*(price*A.liveWidth+ε)+splicedExteriorRate h C β Ht*(price*A.tetherWidth) := by
  subst w
  let W := resetWorld A group B T hub
  refine ⟨reset_value A group B T hub exactBank,
    reset_tether A group B T hub ordinary tether,
    fun e=> (marked_endpoints A group B T hub e).1,fun e=>(marked_endpoints A group B T hub e).2,?_⟩
  apply splice_invoice h C Ht he measured
  have counted := mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (reset_cost A group B T hub): (W.liveWidth:ℝ)≤_) hp
  push_cast at counted ⊢
  change price * (W.liveWidth : ℝ) ≤ _
  linarith only [counted]

end
end Hierarchy.DescentResetAttachments

end OAI
