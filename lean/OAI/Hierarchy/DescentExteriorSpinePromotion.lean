import OAI.Hierarchy.DescentExteriorSpine

namespace OAI
/-! # The same frozen-first exterior matrix accumulates every selected local remix -/

namespace Hierarchy.DescentExterior.Spine
open DescentGL DescentColonies
open scoped Classical
noncomputable section
variable {A B C E:Type} {a b c f g h : ℕ} {raw:E→Bits a} {mid:E→Bits b} {last:E→Bits c}
    {start:E→A} {middle:E→B} {fin:E→C}

def store (width:b+f=a) : (Bits b×Bits f) ≃ₗ[ZMod 2] Bits a :=
  ((LinearEquiv.prodComm _ _ _).trans (splitRows f b).symm).trans (castBits ((Nat.add_comm f b).trans width))

def matrix (x:Spine raw mid start middle f) : Layout a := x.cut.trans (store x.width)

/-- The table uses just the three physical widths and previous stage's fixed
kind. The local matrix comes from the measured mixer. All frozen coordinates
from earlier stages remain inputs to the prescribed permutation. -/
def promoteCut (width:b+f=a) (remaining:c+(g+f)=a)
    (split:Layout h→(Bits b ≃ₗ[ZMod 2] (Bits c×Bits g))) (rotation:Layout h) : Layout a :=
  (((((store width).symm.trans ((split rotation).prodCongr (LinearEquiv.refl _ (Bits f)))).trans
      (LinearEquiv.prodAssoc _ (Bits c) (Bits g) (Bits f))).trans
    ((LinearEquiv.refl _ (Bits c)).prodCongr (splitRows g f).symm)).trans (store remaining))

theorem accumulate (x:Spine raw mid start middle f) (y:Spine mid last middle fin g)
    (split:Layout h→(Bits b ≃ₗ[ZMod 2] (Bits c×Bits g))) (selected:Layout h)
    (used:split selected=y.cut) :
    x.matrix.trans (promoteCut x.width (x.append y).width split selected)=(x.append y).matrix := by
  ext v
  simp only [matrix,promoteCut,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,used,append]

end
end Hierarchy.DescentExterior.Spine

end OAI
