import OAI.Computability.VPVNP.CompressorBlockIndex
import OAI.Computability.VPVNP.CompressorScriptWindow

/-!
# Windows for source runs in the online descriptor script

Each native source trace occupies a contiguous range in the fixed block.
The windows identify the worker for each visit and its ordinal among all
the heterogeneous substeps. They can be applied to the source packets
without numbering the repeated instances of the same instruction table by hand.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockGroups

open PhaseRecipe BlockPlanner Compression

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- The twelve consecutive visit groups of shrinking step `i`, in their order in the compiled
block. -/
def parts (i : Fin S.steps) : List (List Visit) :=
  let step := i.val
  let a := ShrinkBlockInputs.a i
  let F := BlockProgram.geometry B
  let arena := BlockProgram.arena B step
  let origin := arena 0
  let chosen := ShrinkBlockInputs.selectedInputs B F i origin
  let absolute := ShrinkBundlePlan.absoluteCD step a origin
  [BlockHeaderPlan.substep F step (.shrink a (ShrinkBlockInputs.b i)),
   GreedyLevelPlan.visits F step a origin,
   ShrinkBundlePlan.visits F step a origin,
   ShrinkBlockInputs.termVisits B i origin,
   SelectedPlan.visits chosen a,
   ShrinkResidentsPlan.visits chosen (arena 5) (LevelFields.atLevel step) absolute a,
   BlockSlices.intersections i origin (arena 1),
   BlockSlices.surviving B F i origin (arena 2),
   ShrinkBlockInputs.slots B F i origin (arena 3) (arena 2),
   BlockMetadata.visits F step B.recordLimit (slotDegree S) .shrink (.shrink a chosen),
   BlockProgram.termPointers step chosen.termBase (.lit chosen.termStride)
     (SelectedPlan.layout chosen) absolute,
   BlockDataHeads.visits B F i origin (arena 1) (arena 2) (arena 3)]

theorem parts_length (i : Fin S.steps) : (parts B i).length = 12 := rfl

theorem parts_flatten (i : Fin S.steps) : (parts B i).flatten = BlockProgram.shrink B i := by
  simp only [parts,BlockProgram.shrink,ShrinkBlockInputs.beforeSlices,BlockSlices.visits,
    List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]

/-- The seven consecutive groups of the degree refresh, from header publication through the
successor pointer. -/
def refreshParts : List (List Visit) :=
  let step := S.steps
  let F := BlockProgram.geometry B
  let arena := BlockProgram.arena B step
  let p := RefreshBlockPlan.input F step (0 : Fin 6)
  let s := RefreshBlockPlan.shape B
  [BlockHeaderPlan.substep F step (.refresh S.portExponent (S.degreeExponent 0) S.expanderExponent),
   (PortRefresh.LevelRecipe.order s).map (RefreshBlockPlan.stage B p),
   List.ofFn (RefreshBlockPlan.copyColumn B F step p),
   [BlockProgram.refreshPlacement step (arena 4)],
   BlockMetadata.visits F step B.recordLimit (slotDegree S) .refresh (.refresh step (arena 4)),
   BlockProgram.termPointers step (PortRefresh.LevelRecipe.termStart s p) (.lit s.stride) (.lit 0)
     (.lit 0),
   [BlockPlanner.publish (LevelFields.address step 40) (LevelFields.atLevel (step+1))]]

theorem refreshParts_length : (refreshParts B).length = 7 := rfl

theorem refreshParts_flatten : (refreshParts B).flatten = BlockProgram.refresh B := by
  simp only [refreshParts,BlockProgram.refresh,RefreshBlockPlan.visits,List.flatten_cons,
    List.flatten_nil,List.append_nil,List.append_assoc]

private theorem split_groups (ls : List (List Visit)) (j : Fin ls.length) :
    ls.flatten = (ls.take j.val).flatten ++ ls[j.val] ++ (ls.drop (j.val+1)).flatten := by
  have split : ls = ls.take j.val ++ ls[j.val] :: ls.drop (j.val+1) := by
    simpa only [List.drop_eq_getElem_cons j.isLt] using (List.take_append_drop j.val ls).symm
  exact (congrArg List.flatten split).trans
    (by simp only [List.flatten_append,List.flatten_cons,List.append_assoc])

/-- Restrict a script window to its indexed subgroup, moving earlier and later groups into the
surrounding prefix and suffix. -/
def within {A : Script} {body : List Visit} (W : Window A body) (groups : List (List Visit))
    (h : groups.flatten = body) (j : Fin groups.length) : Window A groups[j.val] where
  before := W.before ++ (groups.take j.val).flatten
  after := (groups.drop (j.val+1)).flatten ++ W.after
  block := by
    calc
      A.block = W.before ++ body ++ W.after := W.block
      _ = W.before ++ groups.flatten ++ W.after := congrArg (fun xs ↦ W.before ++ xs ++ W.after)
        h.symm
      _ = _ := by rw [split_groups groups j]; simp only [List.append_assoc]

/-- The window occupied by shrinking step `i` in the complete block script. -/
def shrinkWindow (i : Fin S.steps) : Window (BlockProgram.script B) (BlockProgram.shrink B i) :=
  ⟨BlockIndex.earlier B i,BlockIndex.later B i,BlockIndex.split_block B i⟩

/-- The terminal window of a block, containing the refresh after all shrinking steps. -/
def refreshWindow : Window (BlockProgram.script B) (BlockProgram.refresh B) :=
  ⟨(List.finRange S.steps).flatMap (BlockProgram.shrink B),[],(List.append_nil _).symm⟩

/-- Locate one of the twelve visit groups of a shrinking step in the global script. -/
def shrink (i : Fin S.steps) (j : Fin 12) : Window (BlockProgram.script B)
    ((parts B i)[j.val]'j.isLt) :=
  within (shrinkWindow B i) (parts B i) (parts_flatten B i) j

/-- Locate one of the seven visit groups of the degree refresh in the global script. -/
def refresh (j : Fin 7) : Window (BlockProgram.script B) ((refreshParts B)[j.val]'j.isLt) :=
  within (refreshWindow B) (refreshParts B) (refreshParts_flatten B) j

theorem shrink_offset (i : Fin S.steps) (j : Fin 12) :
    (shrink B i j).before.length = (BlockIndex.earlier B i).length+((parts B i).take
      j.val).flatten.length :=
  List.length_append ..

theorem refresh_offset (j : Fin 7) :
    (refresh B j).before.length = ((List.finRange S.steps).flatMap (BlockProgram.shrink B)).length+
      ((refreshParts B).take j.val).flatten.length := List.length_append ..

end CompressorRecords.BlockGroups

end

end VPVNP
end Computability
end OAI
