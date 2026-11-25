import OAI.Hierarchy.DescentOriginalRangeSlots
import OAI.Hierarchy.DescentRangePage
import OAI.Hierarchy.DescentMetadataInputCore
import OAI.Hierarchy.DescentSliceFields
import OAI.Hierarchy.DescentTerminalSliceRuns
import OAI.Hierarchy.DescentOperandStateCodec

namespace OAI
/-! # The three affine-range words at each flattened operand of a typed gate -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentBundleHistory DescentKernelHistory DescentOperandStateBanks DescentTerminalSliceRuns
noncomputable section
variable {p : ℕ} {U V : Type} {w : V→ℕ} {r : BitRecipe U V w}

theorem layout (s : Shape p r) (u : r.Node) :
    repeatFields (s.sliceFields u).flatten=occurrences s u:=by
  have shape : s.sliceFields u=(s.rows u).map (List.map Slice.code):=by
    simp [Shape.sliceFields,Shape.rows,List.map_ofFn,Function.comp_def]
  rw [shape]
  simp only [repeatFields,List.flatten_eq_flatMap,List.flatMap_assoc,List.flatMap_map,id_eq,
    occurrences,Slice.code]

theorem counts (s : Shape p r) (u : r.Node) :
    (occurrences s u).map SliceCode.count=DescentResetMetadataInputs.argumentSpans s u:=by
  simp [occurrences,DescentResetMetadataInputs.argumentSpans,List.map_flatMap,Slice.code]

theorem atSlot_count (s : Shape p r) (u : r.Node) (j : ℕ) :
    atSlot s u j 2=DescentResetMetadataInputs.argumentSpan s u j := by
  rw [DescentResetMetadataInputs.argumentSpan,←counts s u,List.getElem?_map]
  cases h : (occurrences s u)[j]? <;>simp [atSlot,h,value]

theorem atSlot_padding (s : Shape p r) (u : r.Node) (j : ℕ) (f : Fin 3)
    (outside : (repeatFields (s.sliceFields u).flatten).length≤j) :
    atSlot s u j f=0 := by
  rw [layout] at outside
  simp [atSlot,List.getElem?_eq_none outside]

theorem header (ptr : Pointer) (q : SliceCode) (f : Fin 3) :
    ptr.fields ⟨q.start,q.stride,q.count⟩ (page f)=value q f:=by
  fin_cases f <;> rfl

theorem atSlot_lt (s : Shape p r) (u : r.Node) (f : Fin 3) (j : Fin (repeatFields (s.sliceFields u).flatten).length) :
    atSlot s u j.val f=value (repeatFields (s.sliceFields u).flatten)[j.val] f:=by
  have read : (occurrences s u)[j.val]?=some (repeatFields (s.sliceFields u).flatten)[j.val] :=
    (congrArg (fun rows : List SliceCode => rows[j.val]?) (layout s u).symm).trans
      (List.getElem?_eq_getElem j.isLt)
  simp only [atSlot,read,Option.elim_some]

theorem of_fields {U' V' : Type} {w' : V'→ℕ} {r' : BitRecipe U' V' w'} (t : Shape p r') (v : r'.Node)
    (s : Shape p r) (u : r.Node) (original : t.sliceFields v=s.sliceFields u) (slot : ℕ) (f : Fin 3) :
    atSlot t v slot f=atSlot s u slot f:=by
  have rows : occurrences t v=occurrences s u:=by rw [←layout,←layout,original]
  simp only [atSlot,rows]

theorem restored {K : ℕ} (s : Shape p r) (u : r.Node) (enough : (repeatFields (s.sliceFields u).flatten).length≤K)
    (digits : Fin 3→Fin K→ℕ)
    (read : ∀f j,digits f j=atSlot s u j.val f)
    (j : Fin (repeatFields (s.sliceFields u).flatten).length) :
    (⟨digits 0 (j.castLE enough),digits 1 (j.castLE enough),digits 2 (j.castLE enough)⟩:SliceCode)
      =(repeatFields (s.sliceFields u).flatten)[j.val]:=by
  simp only [read,Fin.val_castLE,atSlot_lt s u _ j]
  cases (repeatFields (s.sliceFields u).flatten)[j.val]
  rfl

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
