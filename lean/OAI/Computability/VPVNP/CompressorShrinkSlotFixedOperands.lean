import OAI.Computability.VPVNP.CompressorShrinkSlotOperandFootprint
import OAI.Computability.VPVNP.CompressorShrinkSlotWindow

/-!
# Physical read addresses of the shrinking slot planners

The fixed block computes its slot operands from the pitch word, the two
level headers and the stored layout bit. The arithmetic locating that bit
includes the two greedy directories, the ranked bundles and the motif terms.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkSlotCalendar

open BurstRAM Compression DescriptorSpace PhaseRecipe ShrinkSlotPlan.Scheduled
open scoped Fin.CommRing

/-- The physical inputs of the slot planners at a shrinking substep. The
fixed level header consists of 54 scalars, six incidence pointers and six
table pointers. -/
def RootCell (pitch old next score x : ℕ) : Prop :=
  x = pitch ∨ (old ≤ x ∧ x < old+66) ∨ (next ≤ x ∧ x < next+66) ∨ x = score

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
  {w : ℕ} {L : DescriptorSpace.Layout} {first : ℕ} {pub : Fin 5 → Word w} {state : Word w}
  {m : Memory w}

/-- Every external load in the inputs of the actual 22-stage program uses
one of the two headers, the pitch word or the selected layout cell. -/
theorem plan_roots (entry : LevelFields.Entry L first pub state m)
    (oldFit : levelStart L (first+i.val)+66 ≤ 2^w)
    (nextFit : levelStart L (first+(i.val+1))+66 ≤ 2^w) :
    Roots (plan B i) (RootCell (pub 1-1).val (levelStart L (first+i.val))
      (levelStart L (first+(i.val+1))) ((SelectedPlan.layoutCell (selected B i)).eval pub state m).val)
      pub state m := by
  let data := RootCell (pub 1-1).val (levelStart L (first+i.val)) (levelStart L (first+(i.val+1)))
    ((SelectedPlan.layoutCell (selected B i)).eval pub state m).val
  let R := Expr.ReadsFrom data pub state m
  have pitch : R LevelFields.stride := ⟨⟨trivial,trivial⟩,Or.inl rfl⟩
  have addr (j offset : ℕ) : R (LevelFields.address j offset) := ⟨⟨trivial,trivial,pitch⟩,trivial⟩
  have old (offset : ℕ) (ho : offset < 66) : R (LevelFields.scalar i.val offset) := by
    refine ⟨addr _ _,?_⟩
    rw [LevelFields.eval_address entry,Fin.val_natCast,Nat.mod_eq_of_lt (by omega)]
    exact Or.inr (Or.inl ⟨Nat.le_add_right ..,by omega⟩)
  have next (offset : ℕ) (ho : offset < 66) : R (LevelFields.scalar (i.val+1) offset) := by
    refine ⟨addr _ _,?_⟩
    rw [LevelFields.eval_address entry,Fin.val_natCast,Nat.mod_eq_of_lt (by omega)]
    exact Or.inr (Or.inr (Or.inl ⟨Nat.le_add_right ..,by omega⟩))
  have vertices := old 0 (by decide)
  have degree := old 1 (by decide)
  have lanes := old 2 (by decide)
  have residual := old 3 (by decide)
  have originRead : R (origin B i) := old 60 (by decide)
  have split : R (BlockProgram.arena B i.val 2) := old 62 (by decide)
  have role : R (BlockProgram.arena B i.val 3) := old 63 (by decide)
  have sites : R (LevelFields.sites i.val) := ⟨vertices,lanes⟩
  have slots : R (LevelFields.slots i.val) := ⟨sites,degree⟩
  have newSites : R (ShrinkBlockInputs.newSites i) := ⟨vertices,trivial,residual⟩
  let a := ShrinkBlockInputs.a i
  let org := origin B i
  have offset : R (GreedyLevelPlan.offsetBase i.val a org) :=
    ⟨⟨originRead,vertices⟩,vertices,trivial⟩
  have shift : R (GreedyLevelPlan.shiftBase i.val a org) :=
    ⟨⟨offset,vertices⟩,vertices,trivial⟩
  have greedy : R (GreedyLevelPlan.greedyStop i.val a org) := ⟨⟨shift,vertices,degree⟩,trivial⟩
  have bundles : R (ShrinkBundlePlan.bundles i.val a) := ⟨newSites,degree⟩
  have owner : R (ShrinkBundlePlan.owner i.val a org) := ⟨greedy,trivial,sites⟩
  have counts : R (ShrinkBundlePlan.counts i.val a org) := ⟨owner,trivial,slots⟩
  have buckets : R (ShrinkBundlePlan.bucketCount i.val a) := ⟨trivial,bundles⟩
  have ids : R (ShrinkBundlePlan.ids i.val a org) := ⟨counts,buckets⟩
  have rectangle : R (ShrinkBundlePlan.rectangle i.val a) := ⟨buckets,trivial⟩
  have sorted : R (ShrinkBundlePlan.sorted i.val a org) := ⟨⟨⟨ids,rectangle⟩,rectangle⟩,slots⟩
  have block : R (ShrinkBundlePlan.blockSize i.val a) := ⟨bundles,trivial⟩
  have ab : R (ShrinkBundlePlan.abStart i.val a org) :=
    ⟨⟨⟨sorted,trivial,block⟩,trivial,block⟩,buckets⟩
  have motifs : R (selected B i).motifs := ⟨bundles,trivial⟩
  have term : R (selected B i).termBase := ⟨⟨ab,trivial,motifs⟩,trivial,motifs⟩
  have score : R (SelectedPlan.scoreBase (selected B i)) := ⟨term,motifs,trivial⟩
  have oldArc : R (plan B i).input.oldArc := ⟨⟨score,trivial⟩,trivial,sites⟩
  have chosen : R (plan B i).layout := ⟨⟨score,trivial⟩,Or.inr (Or.inr (Or.inr rfl))⟩
  have cyclic : R (plan B i).input.nextSite := ⟨role,trivial⟩
  have subdiv : R (plan B i).input.subdivisions := ⟨cyclic,newSites⟩
  refine ⟨vertices,residual,oldArc,role,subdiv,cyclic,⟨subdiv,trivial⟩,chosen,split,?_⟩
  intro c
  exact next (54+c.val) (by have := c.isLt; omega)

end CompressorRecords.ShrinkSlotCalendar

end

end VPVNP
end Computability
end OAI
