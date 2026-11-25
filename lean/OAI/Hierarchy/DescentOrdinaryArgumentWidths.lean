import OAI.Hierarchy.DescentPrimitivePalettePrintedBits
import OAI.Hierarchy.DescentFundedClipChoice
import OAI.Hierarchy.DescentDatedWOrigin
import OAI.Hierarchy.DescentOrdinaryArgumentsAfter
import OAI.Hierarchy.DescentOrdinaryFinalWidth
import OAI.Hierarchy.DescentOrdinaryOriginInvoice

namespace OAI
/-! # The dictionary widths of the physical ordinary argument program -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentRawCablePanel DescentDatedPriorOperand DescentOrdinaryOriginMask
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

def widthTable (source role count chip : ℕ) (refs : DescentOrdinaryRefsROM.Chart)
    (born : DescentOrdinaryBorn.Chart) (vector : DescentOperandVectorArena.Layout)
    (l : DescentDatedPriorOperand.Layout) (R : Return) (B : DescentOrdinaryFinal.Chart)
    (printed nodeBits paidBits : ℕ) : Fin 16 → ℕ :=
  ![source,role,count,chip,refs.keyBits,refs.bits*refs.oldNodes,
    born.chipBits*1+born.chipBits,vector.bookBits,(l.size+2)*l.nodes,
    (l.size+2)+(l.size+2),11*(l.size+2),R.peak,
    (R.ordinalBits*R.newNodes)*1+(R.ordinalBits*R.newNodes),
    B.scalarWidth*B.inputs+B.scalarWidth,
    max (max born.chipBits (born.bits*l.nodes)) printed,
    max (nodeBits*(l.nodes+1)) (max paidBits (l.size+2+nodeBits))]

/-- Width of one lane of each dictionary used by the incoming argument phase.
Both pitches of the archived books are retained in the date entry. -/
def argumentWidths (A : ArgumentEntry v) : Fin 16 → ℕ :=
  let L:=A.population v 0
  widthTable (DescentOrdinaryPriorRetile.digits A.previous) (A.roleLayout v).bits
    (L.countBits*L.donors+L.countBits) (DepotRAM.totalBits (A.chip v).format)
    v.reference v.bornBook v.vector v.resolver v.originChart v.finalChart
    (DescentPrimitivePalette.printedBits v.gadget v.palette.seedWidth v.palette.grainLimit v.palette.rotor)
    v.nodeChart.bits v.metadata.paidBits

/-- Shape-only maximum. Evaluation at zero extra width fixes the public
dimensions of the code before choosing its two physical pitches. -/
def fullArgumentUnit (A : ArgumentEntry v) : ℕ :=
  Finset.univ.sup ((v.withFundedArguments 0 A).argumentWidths (v.fundedEntry 0 A))

section
attribute [local irreducible] DescentOrdinaryVenueIngress.Clip.working DescentOrdinaryVenueIngress.Clip.postPitch
  DescentSIMDLookup.lanes DescentOrdinaryVenueIngress.Clip.unit fundedUnitAt
/-- The list of per-lane widths is invariant under the pitch selection itself. -/
theorem argumentWidths_clip (A : ArgumentEntry v) (extra : ℕ) :
    (v.withFundedArguments extra A).argumentWidths (v.fundedEntry extra A) =
    (v.withFundedArguments 0 A).argumentWidths (v.fundedEntry 0 A) := by
  dsimp only [argumentWidths, widthTable, ArgumentEntry.population, ArgumentEntry.roleLayout,
    ArgumentEntry.chip, finalChart, nodeChart, originChart, withFundedArguments, withFundedClip, fundedEntry]
  rfl
end

theorem argumentWidth_le (A : ArgumentEntry v) (extra : ℕ) (i : Fin 16) :
    (v.withFundedArguments extra A).argumentWidths (v.fundedEntry extra A) i ≤
    v.fullArgumentUnit A := by
  rw [v.argumentWidths_clip A extra]
  exact Finset.le_sup (f:=_) (Finset.mem_univ i)

/-- The other dated consumers may reserve a further finite per-lane width on
the same acquisition. This includes width at the regrouped source and the
vector transpose whose lookup uses one whole radix-sized block. -/
theorem funded_argument_widths (A : ArgumentEntry v) (other : ℕ) (i : Fin 16) :
    let extra:=max (v.fullArgumentUnit A) other
    let c:=v.fundedClip extra
    let width:=(v.withFundedArguments extra A).argumentWidths (v.fundedEntry extra A) i
    width*c.working≤v.payload/4 ∧ (width*c.radix)*c.postPitch≤v.payload/4 ∧
      width*c.postPitch≤v.payload/4 :=
  v.funded_extra_fit _ _ ((v.argumentWidth_le A _ i).trans (Nat.le_max_left _ _))

/-- The real normalizer and the next date's read of its resulting seven
columns both fit at the pitch of the ordinary receiving program. -/
theorem funded_final_widths (A : ArgumentEntry v) (other : ℕ) :
    let extra:=max (v.fullArgumentUnit A) other
    let W:=v.withFundedArguments extra A
    let c:=v.fundedClip extra
    W.finalChart.lookupUnit*c.postPitch≤v.payload/2 ∧
      ((W.resolver.size+2)*W.resolver.nodes)*c.postPitch≤v.payload/2 :=by
  intro extra W c
  have cap : W.finalChart.lookupUnit*c.postPitch≤v.payload/4 :=
    (v.funded_argument_widths A other (13 : Fin 16)).2.2
  have physical : W.finalChart.lookupUnit*c.postPitch≤v.payload/2:=by omega
  exact ⟨physical,(Nat.mul_le_mul_right c.postPitch W.finalChart.return_width_le).trans physical⟩

theorem funded_metadata_widths (A : ArgumentEntry v) (other : ℕ) :
    let extra:=max (v.fullArgumentUnit A) other
    let W:=v.withFundedArguments extra A
    let M:=(v.fundedClip extra).postPitch
    ((W.nodeChart.bits*(W.nodeChart.nodes+1))*M≤v.payload/2) ∧
      max W.metadata.paidBits (W.resolver.size+2+W.nodeChart.bits)*M≤v.payload/2 ∧
      ((W.resolver.size+2)*W.resolver.nodes)*M≤v.payload/2 :=by
  intro extra W M
  let a:=W.nodeChart.bits*(W.nodeChart.nodes+1)
  let b:=max W.metadata.paidBits (W.resolver.size+2+W.nodeChart.bits)
  have cap : max a b*M≤v.payload/4 := (v.funded_argument_widths A other 15).2.2
  have h : max a b*M≤v.payload/2:=by omega
  exact ⟨(Nat.mul_le_mul_right M (Nat.le_max_left a b)).trans h,
    (Nat.mul_le_mul_right M (Nat.le_max_right a b)).trans h,(v.funded_final_widths A other).2⟩

theorem funded_books_room (A : ArgumentEntry v) (other : ℕ) :
    let extra:=max (v.fullArgumentUnit A) other
    let W:=v.withFundedArguments extra A
    W.VectorShape ∧ W.operandBook=W.finalChart ∧
      W.operandBook.lookupUnit*W.operandBook.layout.lanes≤W.payload/2 ∧
      ((W.operandBook.layout.size+2)*W.operandBook.layout.nodes)*W.operandBook.layout.lanes≤W.payload/2 :=by
  intro extra W
  exact ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,v.funded_final_widths A other⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
