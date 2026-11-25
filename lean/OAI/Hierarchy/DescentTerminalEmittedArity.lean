import OAI.Hierarchy.DescentMetadataInputCore
import OAI.Hierarchy.DescentSliceFields
import OAI.Hierarchy.DescentTerminalSliceRuns

namespace OAI
/-! # Flattened arity of the retained operand slices -/
namespace Hierarchy.DescentTerminalSliceRuns
open DescentBundleHistory DescentKernelHistory
open scoped Classical
noncomputable section

variable {U E:Type} {width:E→ℕ} {p:ℕ} {r:BitRecipe U E width} (s:Shape p r) (z:r.Node)
private theorem map_expand (cs:List SliceCode) :
    (repeatFields cs).map SliceCode.count=cs.flatMap (fun c=>List.replicate c.count c.count) := by
  induction cs with
  | nil=>rfl
  | cons c tl ih=>
    change (List.replicate c.count c++repeatFields tl).map _=_++_
    simp [List.map_append,ih]
    exact List.flatMap_def

theorem emitted_spans (hp:0<p) :
    (repeatFields (s.sliceFields z).flatten).map SliceCode.count=DescentResetMetadataInputs.argumentSpans s z := by
  rw [map_expand]
  have eqn:=DescentResetMetadataInputs.tag_spans hp s z
  rw [Shape.tag_fields hp s z] at eqn
  rw [←eqn]
  generalize s.sliceFields z=cs
  unfold DescentResetMetadataInputs.scalarSpans
  induction cs with
  | nil=>rfl
  | cons row rs ih=>simp [List.flatMap_append,ih]


theorem emitted_length (hp:0<p) :
    (repeatFields (s.sliceFields z).flatten).length=(s.recipe hp).arity z := by
  simpa only [List.length_map] using (congrArg List.length (emitted_spans s z hp)).trans
    (DescentResetMetadataInputs.spans_length hp s z)

end
end Hierarchy.DescentTerminalSliceRuns

end OAI
