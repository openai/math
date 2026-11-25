import OAI.Hierarchy.TaggedRadixStatic
import OAI.Hierarchy.TaggedRadixStages

namespace OAI
/-! # Trivalent equality cells for a fixed rectangular row map -/

namespace Hierarchy.Tagged.RadixStage
open ThreeFlat Routing
open scoped Classical
noncomputable section
variable {F : Type*} {I O : Type} [Fintype I] [Fintype O]

def scatterLiteral (v : I ⊕ Bool) : BitSource 0 (Fintype.card (Pins I O Empty)) :=
  v.elim (fun i => .pin (Fintype.equivFin _ (.inl (.inl i)))) BitSource.constant

/-- A static row adapter with one comparison cell for each output bit. -/
def scatterNetwork (F : Type*) [Zero F] [One F] (wire : StaticMap I O) : Network F I O Empty where
  internal := 0
  cells := Fintype.card O
  source k t := let p := (Fintype.equivFin O).symm k
                if t.val = 0 then .pin (Fintype.equivFin _ (.inl (.inr p))) else scatterLiteral (wire p)
  table _ b := if b 0 = b 1 then 1 else 0

@[simp] theorem scatter_cells [Zero F] [One F] (wire : StaticMap I O) :
    (scatterNetwork F wire).cells = Fintype.card O := rfl
@[simp] theorem scatter_internal [Zero F] [One F] (wire : StaticMap I O) :
    (scatterNetwork F wire).internal = 0 := rfl

end
end Hierarchy.Tagged.RadixStage

end OAI
