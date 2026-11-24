import OAI.Computability.VPVNP.CompressorBlockProgram

/-!
# Selector visits in the fixed chronological block

A shrinking selector follows its header, greedy, bundle and dense demand
passes. A refresh selector follows its header, three segment scans and all
tie demands. The ordinal formulas below locate the same native worker in
every repeated block and identify its compiled calendar phase.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockIndex

open PhaseRecipe BlockPlanner Compression

/-- A particular occurrence in a list, recorded with the prefix and suffix that locate it. -/
structure Focus {α : Type*} (items : List α) where
  /-- Entries preceding the distinguished occurrence. -/
  before : List α
  /-- The entry at the distinguished occurrence. -/
  item : α
  /-- Entries following the distinguished occurrence. -/
  after : List α
  split : items = before ++ item :: after

namespace Focus

variable {α : Type*} {items : List α}

/-- Retain the distinguished occurrence when a suffix is appended to the list. -/
def append (F : Focus items) (tail : List α) : Focus (items++tail) :=
  ⟨F.before,F.item,F.after++tail,(congrArg (·++tail) F.split).trans (by simp)⟩

/-- Retain the distinguished occurrence when a prefix is prepended to the list. -/
def prepend (head : List α) (F : Focus items) : Focus (head++items) :=
  ⟨head++F.before,F.item,F.after,(congrArg (head++·) F.split).trans (List.append_assoc ..).symm⟩

/-- Transport a distinguished occurrence along an equality of lists. -/
def cast {other : List α} (h : items = other) (F : Focus items) : Focus other :=
  ⟨F.before,F.item,F.after,h.symm.trans F.split⟩

theorem bound (F : Focus items) : F.before.length < items.length := by
  have h := congrArg List.length F.split
  simp only [List.length_append,List.length_cons] at h
  omega

/-- The zero-based list index of the distinguished occurrence. -/
def index (F : Focus items) : Fin items.length := ⟨F.before.length,F.bound⟩

theorem lookup (F : Focus items) : items[F.index.val] = F.item := by
  have aux (xs ys : List α) (x : α) : (xs++x::ys)[xs.length]'(by simp) = x := by
    rw [List.getElem_append_right le_rfl]; simp
  exact (List.getElem_of_eq F.split _).trans (aux F.before F.after F.item)

end Focus

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- The shrinking motif-selection visit, with its demand count, term-record heads and supply
order. -/
def shrinkSelector (i : Fin S.steps) : Visit :=
  let step := i.val
  let a := ShrinkBlockInputs.a i
  let input := ShrinkBundlePlan.termInputs step a (BlockProgram.arena B step 0)
  ⟨TermWorker.motifPass B.shrink finTwoEquiv 8,.lit 0,ShrinkTermRecipe.count a input,
    TermWorker.motifExprs B.shrink finTwoEquiv SelectedScore.supplyOrder.entries
      (ShrinkTermRecipe.termHeads a 10 input)⟩

private def shrinkPair (i : Fin S.steps) : Focus (ShrinkBlockInputs.termVisits B i
    (BlockProgram.arena B i.val 0)) :=
  ⟨[_],shrinkSelector B i,[],rfl⟩

private def shrinkInput (i : Fin S.steps) :
    Focus (ShrinkBlockInputs.beforeSlices B (BlockProgram.geometry B) i
      (BlockProgram.arena B i.val 0)) :=
  (Focus.prepend _ (shrinkPair B i)).append _

/-- The occurrence of the motif selector in shrinking step `i`. -/
def shrink (i : Fin S.steps) : Focus (BlockProgram.shrink B i) :=
  ((((((shrinkInput B i).append _).append _).append _).append _).append _).append _

theorem shrink_selector (i : Fin S.steps) : (shrink B i).item = shrinkSelector B i := rfl

theorem shrink_offset (i : Fin S.steps) : (shrink B i).before.length = 21 := by
  change ((_ ++ _ ++ _) ++ [_]).length = _
  simp only [List.length_append,BlockHeaderPlan.substep_length,GreedyLevelPlan.visits_length,
    ShrinkBundlePlan.visits_length,List.length_cons,List.length_nil]

/-- The term-selection stage of the degree refresh, evaluated from its published level inputs. -/
def refreshSelector : Visit :=
  RefreshBlockPlan.stage B (RefreshBlockPlan.input (BlockProgram.geometry B) S.steps (0 : Fin 6))
    .term

private def refreshStages : Focus (PortRefresh.LevelRecipe.order (RefreshBlockPlan.shape B)) := by
  let s := RefreshBlockPlan.shape B
  refine ⟨[.gather,.bundles,.offsets] ++ (List.finRange s.ties).map .demand, .term,
    .supply :: (List.finRange (s.ports*s.dH)).map .rom ++ (List.finRange s.degree).map .slot
      ++ [.base],?_⟩
  simp only [PortRefresh.LevelRecipe.order,List.append_assoc,List.cons_append,List.nil_append,s]

private def mapFocus {α β : Type*} {xs : List α} (f : α → β) (F : Focus xs) : Focus (xs.map f) :=
  ⟨F.before.map f,f F.item,F.after.map f,(congrArg (List.map f) F.split).trans (by simp)⟩

/-- The occurrence of the term selector in the complete degree-refresh visit list. -/
def refresh : Focus (BlockProgram.refresh B) :=
  let native := mapFocus (RefreshBlockPlan.stage B (RefreshBlockPlan.input
    (BlockProgram.geometry B) S.steps (0 : Fin 6)))
    (refreshStages B)
  ((((Focus.prepend _ (native.append _)).append _).append _).append _).append _

theorem refresh_selector : (refresh B).item = refreshSelector B := rfl

theorem refresh_offset : (refresh B).before.length = 6+(RefreshBlockPlan.shape B).ties := by
  simp only [refresh,Focus.append,Focus.prepend,mapFocus,refreshStages,List.length_append,
    BlockHeaderPlan.substep_length, List.length_map, List.length_cons, List.length_nil,
      List.length_finRange]
  omega

/-- All shrinking visits in the block strictly before step `i`. -/
def earlier (i : Fin S.steps) : List Visit :=
  ((List.finRange S.steps).take i.val).flatMap (BlockProgram.shrink B)

/-- The shrinking visits strictly after step `i`, followed by the block's refresh. -/
def later (i : Fin S.steps) : List Visit :=
  ((List.finRange S.steps).drop (i.val+1)).flatMap (BlockProgram.shrink B) ++ BlockProgram.refresh B

theorem split_block (i : Fin S.steps) :
    BlockProgram.block B = earlier B i ++ BlockProgram.shrink B i ++ later B i := by
  let ls := List.finRange S.steps
  have hi : i.val < ls.length := by simp [ls]
  have elem : ls[i.val] = i := by simp [ls]
  have split : ls = ls.take i.val ++ i :: ls.drop (i.val+1) := by
    conv_lhs => rw [← List.take_append_drop i.val ls, List.drop_eq_getElem_cons hi, elem]
  change ls.flatMap (BlockProgram.shrink B) ++ _ = _
  conv_lhs => rw [split]
  simp only [earlier,later,ls,List.flatMap_append,List.flatMap_cons,List.append_assoc]

/-- The occurrence of step `i`'s shrinking selector in the complete block. -/
def blockShrink (i : Fin S.steps) : Focus (BlockProgram.block B) :=
  ((Focus.prepend (earlier B i) (shrink B i)).append (later B i)).cast (split_block B i).symm

/-- The occurrence of the refresh selector in the complete block after all shrinking visits. -/
def blockRefresh : Focus (BlockProgram.block B) :=
  Focus.prepend ((List.finRange S.steps).flatMap (BlockProgram.shrink B)) (refresh B)

theorem block_shrink_offset (i : Fin S.steps) : (blockShrink B i).index.val =
    (earlier B i).length+21 := by
  change ((earlier B i) ++ (shrink B i).before).length = _
  rw [List.length_append,shrink_offset]

theorem block_refresh_offset : (blockRefresh B).index.val =
    ((List.finRange S.steps).flatMap (BlockProgram.shrink B)).length +
      (6+(RefreshBlockPlan.shape B).ties) := by
  change (_ ++ (refresh B).before).length = _
  rw [List.length_append,refresh_offset]

theorem selector_at {t : ℕ} (F : Focus (BlockProgram.block B)) :
    let A := BlockProgram.script B
    let j := F.index
    let physical := j.natAdd A.initial.length
    let ordinal := A.initial.length+t*A.block.length+j.val
    A.visit physical = F.item ∧
    (Schedule.Online.calendar A.plan).phase ordinal = physical.val ∧
    (Schedule.Online.calendar A.plan).level ordinal = t := by
  intro A j physical ordinal
  exact ⟨(A.block_visit j).trans F.lookup,A.block_phase t j⟩

end CompressorRecords.BlockIndex

end

end VPVNP
end Computability
end OAI
