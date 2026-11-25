import OAI.Hierarchy.TaggedWideCalendarPinGeometry

namespace OAI
/-! # Fully charged gather and barrel circuits at a single transition -/

noncomputable section
namespace Hierarchy.Tagged.ChordAperture
open ThreeFlat Routing
open scoped Classical BigOperators
variable {F I V : Type} [Field F] [Fintype I] [Fintype V] {bits width : ℕ}
local notation "HS" => I×Fin width
local notation "Pin" => BinaryBarrelTurns.Pin (BinaryBarrelTurns.digits width) (BinaryBarrelTurns.digits width) width

theorem padding_cost (ctl : I→Fin bits→V) :
    let p:=padding (F:=F) (W:=width) ctl
    p.cells+p.internal≤Fintype.card I*(width*(200*bits+65)) := by
  intro p
  rw [show p.cells+p.internal=_ from WideHost.localFamily_size ..]
  calc
    _≤∑_ : I,width*(200*bits+65) := Finset.sum_le_sum fun _ _=>WidePadding.Ports.cost (F:=F) _
    _=_ := by simp

/-- Includes the real hidden word and both the dynamic zero-extension check
and all pairwise barrels, in addition to the selected consumer's own price. -/
theorem attach_cost (cut : I×I→Pin→(V⊕HS)⊕Bool) (ctl : I→Fin bits→V)
    (consumer : BitNetwork F (Fintype.card (V⊕HS))) :
    let n:=attach cut ctl consumer
    n.cells+n.internal≤Fintype.card I*width+Fintype.card I*(width*(200*bits+65))+
      Fintype.card I*Fintype.card I*(2308*width*(width.log2+2))+(consumer.cells+consumer.internal) := by
  dsimp only
  rw [fee]
  have masks:=padding_cost (F:=F) (width:=width) ctl
  have barrels:=PassiveWindow.cost (F:=F) cut
  change (pairsNet (F:=F) cut).cells+(pairsNet (F:=F) cut).internal≤_ at barrels
  simp only [Fintype.card_prod,Fintype.card_fin]
  omega

end Hierarchy.Tagged.ChordAperture

end
end OAI
