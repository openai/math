import OAI.Hierarchy.DescentDatedPhysicalOrdinary
import OAI.Hierarchy.DescentOrdinaryPaletteLayout
import OAI.Hierarchy.DescentOrdinaryPaletteBirthLayout
import OAI.Hierarchy.DescentPrimitivePalettePrintedBits

namespace OAI
/-! Public address of the complete primitive archive, relative to the preceding operand book. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryPrimitiveCheckpoint DescentPrimitivePalette
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

def paletteShape : Layout :=
  ⟨v.vector.hosts,v.reference.degree,v.reference.k,v.reference.capacity,v.vector.lows,v.vector.groups,
    v.reference.oldNodes,v.resolver.nodes,printedBits v.gadget v.palette.seedWidth v.palette.grainLimit v.palette.rotor,
    Nat.clog 2 (v.reference.nodes+1),v.rasterLanes,v.bornBook.lanes,v.vector.lanes,
    v.palette.workLanes,v.palette.nextLanes⟩

def primitiveFirst (operandStop : ℕ) :=DescentOrdinaryPaletteBirth.roof v.bornBook operandStop
def primitiveRoof (operandStop : ℕ) :=v.paletteShape.roof (v.primitiveFirst operandStop)
def primitiveBank (operandStop : ℕ) (x : Fin (2^v.reference.k)) :=v.paletteShape.bank (v.primitiveFirst operandStop) x

theorem primitive_spent (operandStop : ℕ) :
    v.primitiveRoof operandStop=operandStop+v.primitiveRoof 0 ∧ operandStop≤v.primitiveRoof operandStop:=by
  have a:=v.paletteShape.translated (v.primitiveFirst operandStop)
  have b:=v.paletteShape.translated (v.primitiveFirst 0)
  have eqn : v.primitiveRoof operandStop=operandStop+v.primitiveRoof 0:=by
    unfold primitiveRoof
    rw [a,b]
    simp only [primitiveFirst,DescentOrdinaryPaletteBirth.translated,Nat.zero_add,Nat.add_assoc]
  exact ⟨eqn,by rw [eqn];exact Nat.le_add_right ..⟩
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
