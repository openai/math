import OAI.Hierarchy.DescentSeedPackedHeaderNumbers
import OAI.Hierarchy.DescentExteriorCoordinates
import OAI.Hierarchy.DescentExteriorHeader
import OAI.Hierarchy.DescentNativeInput

namespace OAI
/-! # Exterior chunk indices are genuine independently copied public pins -/
namespace Hierarchy.DescentExterior
open DescentGL DescentColonies DescentInitialHost DescentSixParty Computability.BorderVNP.Crossing CorrectionFrame
open ThreeFlat Routing Catalyst CatalystSubstitution CorrectionBatch
open scoped Classical BigOperators
noncomputable section

theorem address_cast {k n : ℕ} (eq : k=n) (x : Bits k) :
    (address n (castBits eq x)).val=(address k x).val := by subst n;rfl

theorem coordinate_row (j r : ℕ) (x : Bits (j+(j+r))) :
    (address _ x).val=(rowOrd j r (coords j r x).2).val*2^j+
      (chunkOrd j (coords j r x).1).val := by
  rw [←address_cast (Nat.add_comm j (j+r)) x,split_value (j+r) j]
  simp [rowOrd,chunkOrd,coords,LinearEquiv.trans_apply]

variable {F : Type} [Field F] {arity data : ℕ} (X : Approximation F arity data) {j r t : ℕ}
local notation "k" => j+(j+r)
def publicPin (a : Fin (ExteriorCount X)) (v : Plane j r) (b : Fin t) :
    Catalyst.Port ((2^k*t)*data) (copiesWidth (2^k*t) X.width) :=
  copiesPortEquiv (p:=data) (2^k*t) X.width (finProdFinEquiv (address _ ((coords j r).symm v),b),
    (Fintype.equivFin (Catalyst.Port data X.width)).symm a)

def publicRows (x : Catalyst.Port ((2^k*t)*data) (copiesWidth (2^k*t) X.width)→Bool)
    (a : Fin (ExteriorCount X)) (v : Plane j r) (b : Fin t) := x (publicPin X a v b)

omit [Field F] in
theorem public_read (x : Catalyst.Port ((2^k*t)*data) (copiesWidth (2^k*t) X.width)→Bool)
    (a : Fin (ExteriorCount X)) (v : Plane j r) (b : Fin t) :
    publicRows X x a v b=packagePins X (2^k) t x ⟨address _ ((coords j r).symm v),a⟩
      (finProdFinEquiv (b,(0:Fin 1))) := by
  simp [publicRows,publicPin,packagePins,stackRows]

omit [Field F] in
theorem final_public_read (M : Fin (ExteriorCount X)→Layout k)
    (x : Catalyst.Port ((2^k*t)*data) (copiesWidth (2^k*t) X.width)→Bool)
    (z : Hidden (ExteriorCount X) j r t→Bool)
    (ok : ∀a,stagesOK (M a) (publicRows X x a) (projected z false a) (projected z true a))
    (a : Fin (ExteriorCount X)) (i : Bits k) (b : Fin t) :
    output (M a) (projected z true a) (coords j r (M a i)) b =
      packagePins X (2^k) t x ⟨address _ i,a⟩ (finProdFinEquiv (b,(0:Fin 1))) := by
  rw [output_wire (M a) (publicRows X x a) _ _ (ok a) i,public_read,LinearEquiv.symm_apply_apply]

end
end Hierarchy.DescentExterior

end OAI
