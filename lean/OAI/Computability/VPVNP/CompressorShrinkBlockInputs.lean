import OAI.Computability.VPVNP.CompressorShrinkBundlePlan
import OAI.Computability.VPVNP.CompressorShrinkSelectedPlan
import OAI.Computability.VPVNP.CompressorShrinkSlotPlan
import OAI.Computability.VPVNP.CompressorBlockHeaderPlan

/-!
# Connecting the shrinking passes to the fixed block

A single persistent arena starts with the two greedy directories. The
ranked AB and CD inputs determine the fused motif worker's term addresses.
The stored terms determine the score, selected placement, arc roles and
child directory. All later slot visitors read the same common layout bit.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkBlockInputs

open BurstRAM PhaseRecipe BlockPlanner Compression Compression.ShrinkMotif

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  (F : DescriptorSpace.Shape) (i : Fin S.steps)

/-- The input degree exponent of this shrinking substep in the block schedule. -/
abbrev a (i : Fin S.steps) := S.degreeExponent i.castSucc
/-- The degree exponent of the output level produced by this shrinking substep. -/
abbrev b (i : Fin S.steps) := S.degreeExponent i.succ

/-- Expression for the packed output site count, multiplying the base-vertex count by the tag
count and residual lane count. -/
def newSites := (LevelFields.vertices i.val).mul
  ((Expr.lit (2^(Shrink.J (a i)))).mul (LevelFields.residualLanes i.val))

/-- The fixed tag, degree, color and subdivision parameters used to build the ordered output
slots of this shrinking substep. -/
def slotTemplate : ShrinkSlotPlan.Template :=
  let d := 2^(a i)
  let c := Shrink.colors (a i)
  let d' := 2^(b i)
  ⟨2^(Shrink.J (a i)),d,c,subdivisions d c d',d'⟩

/-- The physical motif table has a grid index, a repetition count and eight
supply coordinates for the two layouts. -/
def termVisits (origin : Expr) : List Visit :=
  let I := ShrinkBundlePlan.termInputs i.val (a i) origin
  let count := ShrinkTermRecipe.count (a i) I
  let src := ShrinkDemandGather.pass
  let term := TermWorker.motifPass B.shrink finTwoEquiv 8
  [⟨src,.lit 0,count,ShrinkTermRecipe.gatherOperands (a i) I⟩,
   ⟨term,.lit 0,count,TermWorker.motifExprs B.shrink finTwoEquiv SelectedScore.supplyOrder.entries
      (ShrinkTermRecipe.termHeads (a i) 10 I)⟩]

/-- The level sizes, term-record addresses, selector width and placement operands needed to
score and materialize a selected shrinking term. -/
def selectedInputs (origin : Expr) : SelectedPlan.Inputs :=
  let I := ShrinkBundlePlan.termInputs i.val (a i) origin
  ⟨LevelFields.sites i.val,newSites i,LevelFields.slots i.val,ShrinkTermRecipe.count (a i) I,
    ShrinkTermRecipe.term (a i) I,10,B.shrink.selectorBits,ShrinkBundlePlan.placementParams F
      i.val (a i) origin,
    LevelFields.incidence F i.val 3⟩

/-- Role offsets, subdivision counts, cyclic successor and the append/sort
workspace occupy disjoint intervals of the slot arena. -/
def slotInputs (origin slotArena : Expr) : ShrinkSlotPlan.Inputs :=
  let chosen := selectedInputs B F i origin
  let cyclic := slotArena.add (.lit 8)
  let subdiv := cyclic.add (newSites i)
  ⟨LevelFields.vertices i.val,LevelFields.residualLanes i.val,SelectedPlan.roleBase chosen,
    slotArena,subdiv,cyclic,subdiv.add (.lit 4)⟩

/-- The deterministic header and greedy visits, followed by bundle preparation, term choice and
selected placement before the slice scans. -/
def beforeSlices (origin : Expr) : List Visit :=
  BlockHeaderPlan.substep F i.val (.shrink (a i) (b i)) ++
    GreedyLevelPlan.visits F i.val (a i) origin ++ ShrinkBundlePlan.visits F i.val (a i) origin ++
    termVisits B i origin ++ SelectedPlan.visits (selectedInputs B F i origin) (a i)

/-- Generate the ordered output-slot visits using this substep's template, selected layout bit,
slot arena and split index. -/
def slots (origin slotArena split : Expr) : List Visit :=
  ShrinkSlotPlan.visits (slotTemplate i) (slotInputs B F i origin slotArena)
    (SelectedPlan.layout (selectedInputs B F i origin)) split F i.val

theorem termVisits_length (origin : Expr) : (termVisits B i origin).length = 2 := rfl

theorem beforeSlices_length (origin : Expr) : (beforeSlices B F i origin).length = 36 := by
  simp only [beforeSlices, List.length_append, BlockHeaderPlan.substep_length,
    GreedyLevelPlan.visits_length,
    ShrinkBundlePlan.visits_length,termVisits_length,SelectedPlan.visits_length]

theorem slots_length (origin slotArena split : Expr) : (slots B F i origin slotArena split).length
    = 22 :=
  ShrinkSlotPlan.visits_length ..

theorem slot_shape {g : ℕ} (X : State (a i) (packingLaneBits (a i) g)) :
    (slotTemplate i).shape (Fintype.card X.Base) (2^g) = ShrinkSlots.levelShape (b := b i) X := rfl

end CompressorRecords.ShrinkBlockInputs

end

end VPVNP
end Computability
end OAI
