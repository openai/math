import OAI.Hierarchy.DescentExteriorSpinePromotion
import OAI.Hierarchy.DescentExteriorMatrixUpdate

namespace OAI
/-! # The same frozen-first exterior matrix accumulates every selected local remix -/

namespace Hierarchy.DescentExterior.Spine
open DescentGL DescentColonies
open scoped Classical
noncomputable section
variable {A B C E:Type} {a b c f g h : ℕ} {raw:E→Bits a} {mid:E→Bits b} {last:E→Bits c}
    {start:E→A} {middle:E→B} {fin:E→C}

theorem packed_update (x:Spine raw mid start middle f) (y:Spine mid last middle fin g)
    (split:Layout h→(Bits b ≃ₗ[ZMod 2] (Bits c×Bits g))) (selected:Layout h)
    (used:split selected=y.cut) :
    DescentExteriorMatrixUpdate.entry (promoteCut x.width (x.append y).width split)
      (matrixCode x.matrix) (matrixCode selected)=
      matrixCode (x.append y).matrix := by
  rw [DescentExteriorMatrixUpdate.entry_read,accumulate x y split selected used]

end
end Hierarchy.DescentExterior.Spine

end OAI
