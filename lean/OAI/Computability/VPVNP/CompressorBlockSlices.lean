import OAI.Computability.VPVNP.CompressorShrinkBlockInputs
import OAI.Computability.VPVNP.CompressorShrinkABSliceRecipe
import OAI.Computability.VPVNP.CompressorSurvivingNative

/-!
# Physical AB intersections and selected-role subdivisions of a block

The AB stage pairs the thick sorted fields with the new AB widths in the
same bundle. The four selected-role stages recover the absolute motif ID,
read its chosen supply coordinate and write both the split width and the
singleton intersection record. The subsequent slot pass reads those
physical split widths.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockSlices

open BurstRAM PhaseRecipe BlockPlanner Compression ShrinkSliceSweep
open ShrinkBlockInputs

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  (F : DescriptorSpace.Shape) (i : Fin S.steps)

/-- Address operands for intersecting the sorted old thick-wire intervals with the new AB
intervals in each bundle. -/
def abInputs (origin abArena : Expr) : ShrinkABSliceRecipe.Inputs :=
  let thick := ShrinkBundlePlan.prefixParams i.val (a i) origin false
  let fresh := ShrinkBundlePlan.abParams i.val (a i) origin
  ⟨ShrinkBundlePlan.bundles i.val (a i),thick 3,thick 2,thick 1,fresh 4,fresh 3,fresh 1,abArena⟩

/-- The AB interval-intersection scans for the given shrinking step and its fixed thick-wire
and bundle capacities. -/
def intersections (origin abArena : Expr) : List Visit :=
  ShrinkABSliceRecipe.visits (abInputs i origin abArena) (ShrinkBundlePlan.thickCount (a i))
    (ShrinkBundlePlan.cap (a i))

/-- Total subdivision count across the shrinking slot template. -/
def subdivisionSum := ∑ t, (slotTemplate i).subdivisions t

/-- Address of the surviving-interval array following the four width columns for each slot
subdivision. -/
def intervals (widthArena : Expr) : Expr :=
  widthArena.add (((Expr.lit 4).mul (LevelFields.slots i.val)).mul (.lit (subdivisionSum i)))

/-- The physical motif, term, layout, width and interval operands used to compute the surviving
subdivisions. -/
def survivingHeads (origin widthArena : Expr) : SurvivingNative.Heads :=
  let chosen := selectedInputs B F i origin
  ⟨chosen.motifs,chosen.termBase,.lit chosen.termStride,ShrinkBundlePlan.absoluteCD i.val
    (a i) origin,
    SelectedPlan.layoutCell chosen,.lit chosen.selectorBits,widthArena,intervals i widthArena⟩

/-- The native phases that read the selected terms and write the surviving subdivision widths
and intervals. -/
def surviving (origin widthArena : Expr) : List Visit :=
  SurvivingNative.phases (slotTemplate i).subdivisions (survivingHeads B F i origin widthArena)

/-- The shrinking slice visits in order, first AB intersections and then surviving-role
subdivisions. -/
def visits (origin abArena widthArena : Expr) : List Visit :=
  intersections i origin abArena ++ surviving B F i origin widthArena

theorem visits_length (origin abArena widthArena : Expr) :
    let m := ShrinkBundlePlan.thickCount (a i)
    let n := ShrinkBundlePlan.cap (a i)
    (visits B F i origin abArena widthArena).length = m+n+2*(m*n)+4 := by
  simp only [visits,intersections,surviving,List.length_append,ShrinkABSliceRecipe.visits_length,
    SurvivingNative.phases,List.length_ofFn]

theorem split_source (origin widthArena : Expr) :
    (survivingHeads B F i origin widthArena).widthBase = widthArena := rfl

theorem ab_operands (origin abArena : Expr) :
    (abInputs i origin abArena).oldStarts = ShrinkBundlePlan.prefixStart i.val (a i) origin ∧
    (abInputs i origin abArena).oldWidths = ShrinkBundlePlan.sorted i.val (a i) origin ∧
    (abInputs i origin abArena).newWidths = ShrinkBundlePlan.abStart i.val (a i) origin ∧
    (abInputs i origin abArena).newStarts =
      (ShrinkBundlePlan.abStart i.val (a i) origin).add (ShrinkBundlePlan.blockSize i.val (a i)) :=
  ⟨rfl,rfl,rfl,rfl⟩

end CompressorRecords.BlockSlices

end

end VPVNP
end Computability
end OAI
