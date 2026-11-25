import OAI.Hierarchy.DescentRotorPublicOperand
import OAI.Hierarchy.DescentOrderedRotorDigits
import OAI.Hierarchy.DescentRotorWindowArchive

namespace OAI
namespace Hierarchy.DescentRotorOperandQueryROM.Shape
open DescentSIMDLookup DescentPhysicalSplit DescentBatchedNodeOrder DescentRotor DescentLaneGates
open DescentBaseProfile DescentCommonHost DescentHostDirectory DescentDenseHostOrder DescentResetHostSize DescentResetLaneIssue
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical Fin.CommRing
noncomputable section
variable {n h : ℕ} (G : NonlinearExpanders.Graph n h) (C : Shape)
local notation "Q" => DescentCommonPalette.rotor G
local notation "H₀" => Physical.host G.arcs 0 0 0 0 0

/-- The first private lane of a selected tap precedes the public lane, even when
the affine spine uses several p-word arguments. -/
theorem public_selector_none (mult p node arg : ℕ) (x : Fin 4→Cell C.fieldBits) (side : Bool) (key : Code C.residual)
    (v : (Q).Site) (shape : ↥(roster G C.residual C.depth))
    (depth : (x 1).val=key.val.1+1) (safe : (x 2).val%2=0)
    (seen : (x 3).val=(localRank G C.residual C.depth shape).val) (good : shape.val=.good side ((),key.val.2) v)
    (socket : C.publicTap G mult (DescentRecordedRotorLayers.layers n C.packet C.gain (x 0).val) p node arg v=none) :
    C.public_selector G mult p node arg x=none :=by
  have real : (x 3).val<(roster G C.residual C.depth).card:=seen ▸ (localRank G C.residual C.depth shape).isLt
  have actual : (⟨(x 3).val,real⟩ : Fin (roster G C.residual C.depth).card)=
      DescentResetTrunkPalette.order G C.residual C.depth shape:=Fin.ext seen
  simp [public_selector,safe,depth,real,actual,good,key.property,socket]

theorem public_spine_none (mult layers p arg : ℕ) (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count H₀ v))
    (r : SpineRow (r:=layers) (m:=C.batches) (C.subrow G mult v)) :
    C.publicTap G mult layers p (tapOrder layers C.batches (C.subrow G mult v) i (.inl r)).val arg ⟨v,.inr i⟩=none:=by
  simp [publicTap]

theorem public_private_none (mult layers p arg : ℕ) (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count H₀ v))
    (t : Block layers C.batches (C.subrow G mult v i)) (wire) (edge : name H₀ v i=.inr wire) :
    C.publicTap G mult layers p (tapOrder layers C.batches (C.subrow G mult v) i (.inr t)).val arg ⟨v,.inr i⟩=none:=by
  simp [publicTap,edge]

end
end Hierarchy.DescentRotorOperandQueryROM.Shape

end OAI
