import OAI.Computability.VPVNP.CompressorBlockProgram
import OAI.Computability.VPVNP.CompressorPublishedHeadsRun

/-!
# Memory read by the published term and DFS heads

The address formulas use four scalar words of the old level, its table
heads and the block pitch. The selected shrinking layout needs one more
read from the score table. Each of these cells is outside the fields
published at offsets 36 through 53.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockHeadStability

open BurstRAM BurstRAM.PrivateRAM DescriptorSpace PhaseRecipe LevelFields Compression SourceTransport
open scoped Fin.CommRing

variable {w : ℕ} {pub : Fin 5 → Word w} {state : Word w} {original mem : Memory w}
variable {L : Layout} {first : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

private abbrev same (pub : Fin 5 → Word w) (state : Word w) (mem original : Memory w) (e : Expr) :=
  e.eval pub state mem = e.eval pub state original

private theorem eval_add (p : Fin 5 → Word w) (s : Word w) (m : Memory w) (x y : Expr) :
    (x.add y).eval p s m = x.eval p s m + y.eval p s m := rfl

private theorem eval_mul (p : Fin 5 → Word w) (s : Word w) (m : Memory w) (x y : Expr) :
    (x.mul y).eval p s m = x.eval p s m * y.eval p s m := rfl

private theorem eval_lit (p : Fin 5 → Word w) (s : Word w) (m : Memory w) (n : ℕ) :
    (Expr.lit n).eval p s m = (n : Word w) := rfl

/-- The only old-header reads in the compiled expressions. -/
private structure Inputs (step : ℕ) (pub : Fin 5 → Word w) (state : Word w) (mem original : Memory w) : Prop where
  vertex : same pub state mem original (vertices step)
  deg : same pub state mem original (degree step)
  lane : same pub state mem original (lanes step)
  residual : same pub state mem original (residualLanes step)
  arena (j : Fin 6) : same pub state mem original (BlockProgram.arena B step j)
  next : same pub state mem original (atLevel (step+1))

/-- A block pointer places its pitch cell before every graph header. -/
theorem pitch_before (first step : ℕ) (dir : pub 1 = ((directoryBase L) : Word w))
    (fit : directoryBase L < 2^w) : (pub 1-1).val < levelStart L (first+step)+36 := by
  have pos : 1 ≤ directoryBase L := Nat.le_add_left ..
  have wsub : pub 1-1 = ((directoryBase L-1 : ℕ) : Word w) := by rw [dir,Nat.cast_sub pos,Nat.cast_one]
  rw [wsub,Fin.val_natCast,Nat.mod_eq_of_lt ((Nat.sub_le ..).trans_lt fit)]
  have below : directoryBase L ≤ levelStart L (first+step) :=
    (Nat.le_add_right .. : directoryBase L ≤ levelsBase L).trans (Nat.le_add_right ..)
  omega

private theorem readInputs {step offset N : ℕ} (entry : Entry L first pub state original)
    (room : levelStart L (first+step)+66 ≤ 2^w) (pitch : (pub 1-1).val < levelStart L (first+step)+36)
    (lo : 36 ≤ offset) (hi : offset+N ≤ 54)
    (frame : Agree (PublishedHeads.Outside (levelStart L (first+step)+offset) N) mem original) :
    Inputs B step pub state mem original := by
  let base := levelStart L (first+step)
  have pitchKeep : mem (pub 1-1).val = original (pub 1-1).val :=
    frame _ (.inl (pitch.trans_le (Nat.add_le_add_left lo _)))
  have afterEntry : Entry L first pub state mem := ⟨entry.pointer,pitchKeep.trans entry.pitch⟩
  have scalarKeep (j : ℕ) (small : j < 66) (apart : j < 36 ∨ 54 ≤ j) :
      same pub state mem original (scalar step j) := by
    have fits : base+j < 2^w := (Nat.add_lt_add_left small _).trans_le room
    rw [same,eval_scalar afterEntry step j fits,eval_scalar entry step j fits]
    exact frame _ (apart.imp (fun h => Nat.add_lt_add_left (h.trans_le lo) _)
      (fun h => by change base+offset+N ≤ base+j; omega))
  refine ⟨scalarKeep 0 (by decide) (by decide),scalarKeep 1 (by decide) (by decide),
    scalarKeep 2 (by decide) (by decide),scalarKeep 3 (by decide) (by decide),fun j => ?_,?_⟩
  · change same pub state mem original (scalar step (54+6+j.val))
    exact scalarKeep _ (by have := j.isLt; omega) (.inr (by omega))
  · exact (eval_atLevel afterEntry (step+1)).trans (eval_atLevel entry (step+1)).symm

open private recordsEnd firstRecord from OAI.Computability.VPVNP.CompressorGreedyLevelPlan

variable (i : Fin S.steps)

private abbrev F := BlockProgram.geometry B
private abbrev origin := BlockProgram.arena B i.val 0
private abbrev chosen := ShrinkBlockInputs.selectedInputs B (F B) i (origin B i)
private abbrev a := ShrinkBlockInputs.a i

private theorem bundle_heads (h : Inputs B i.val pub state mem original) :
    let st := i.val
    let d := a i
    let o := origin B i
    same pub state mem original (ShrinkBundlePlan.owner st d o) ∧
    same pub state mem original (ShrinkBundlePlan.ranks st d o) ∧
    same pub state mem original (ShrinkBundlePlan.ids st d o) ∧
    same pub state mem original (ShrinkBundlePlan.sorted st d o) ∧
    same pub state mem original (ShrinkBundlePlan.prefixStart st d o) ∧
    same pub state mem original (ShrinkBundlePlan.abStart st d o) ∧
    same pub state mem original (ShrinkBundlePlan.absoluteCD st d o) ∧
    same pub state mem original (ShrinkBundlePlan.blockSize st d) := by
  simp only [same,ShrinkBundlePlan.absoluteCD,ShrinkBundlePlan.prefixStart,ShrinkBundlePlan.abStart,
    ShrinkBundlePlan.totalStart,ShrinkBundlePlan.sorted,ShrinkBundlePlan.ranks,ShrinkBundlePlan.gathered,
    ShrinkBundlePlan.ids,ShrinkBundlePlan.counts,ShrinkBundlePlan.owner,ShrinkBundlePlan.preliminary,
    ShrinkBundlePlan.rectangle,ShrinkBundlePlan.bucketCount,ShrinkBundlePlan.blockSize,ShrinkBundlePlan.bundles,
    GreedyLevelPlan.greedyStop,GreedyLevelPlan.zeroAddress,GreedyLevelPlan.shiftBase,GreedyLevelPlan.offsetBase,
    recordsEnd,firstRecord,sites,slots,origin,eval_add,eval_mul,eval_lit,h.arena,h.vertex,h.deg,h.lane,h.residual,
    and_self]

private theorem selected_heads (h : Inputs B i.val pub state mem original) :
    let c := chosen B i
    let terms := ShrinkBundlePlan.termInputs i.val (a i) (origin B i)
    same pub state mem original c.termBase ∧ same pub state mem original (ShrinkTermRecipe.dense (a i) terms) ∧
    same pub state mem original (SelectedPlan.roleBase c) ∧ same pub state mem original (SelectedPlan.layoutCell c) := by
  have hab := (bundle_heads B i h).2.2.2.2.2.1
  simp only [same,chosen,ShrinkBlockInputs.selectedInputs,SelectedPlan.roleBase,SelectedPlan.placementBase,
    SelectedPlan.layoutCell,SelectedPlan.scoreBase,ShrinkTermRecipe.term,ShrinkTermRecipe.dense,ShrinkTermRecipe.count,
    ShrinkTermRecipe.bundles,ShrinkBundlePlan.termInputs,sites,eval_add,eval_mul,eval_lit,
    h.vertex,h.deg,h.lane,h.residual,hab,and_self]

private theorem slot_heads (h : Inputs B i.val pub state mem original) :
    let ar := BlockProgram.arena B i.val 3
    let c := SlotLevel.Recipe.counts (ShrinkBlockInputs.slotTemplate i)
      (ShrinkBlockInputs.slotInputs B (F B) i (origin B i) ar)
    same pub state mem original c.rows ∧ same pub state mem original c.inverse := by
  simp only [same,SlotLevel.Recipe.counts,ShrinkBlockInputs.slotInputs,ShrinkBlockInputs.newSites,
    eval_add,eval_mul,eval_lit,h.arena,h.vertex,h.residual,and_self]

/-- The selected score bit lies after the publication window whenever the
term region starts beyond the header and the final score offset fits. -/
theorem layoutCell_after (base term rows : ℕ)
    (ht : (chosen B i).termBase.eval pub state original = (term : Word w))
    (hn : (chosen B i).motifs.eval pub state original = (rows : Word w)) (low : base+54 ≤ term)
    (fit : term+rows*(chosen B i).termStride+2 < 2^w) :
    base+54 ≤ ((SelectedPlan.layoutCell (chosen B i)).eval pub state original).val := by
  have hw : (SelectedPlan.layoutCell (chosen B i)).eval pub state original =
      ((term+rows*(chosen B i).termStride+2 : ℕ) : Word w) := by
    simp only [SelectedPlan.layoutCell,SelectedPlan.scoreBase,eval_add,eval_mul,eval_lit,ht,hn,Nat.cast_add,Nat.cast_mul]
  rw [hw,Fin.val_natCast,Nat.mod_eq_of_lt fit]
  omega

/-- RHS expressions at offsets 36 through 39 on a shrinking substep. -/
def shrinkTerms : Fin 4 → Expr :=
  ![(chosen B i).termBase,.lit (chosen B i).termStride,SelectedPlan.layout (chosen B i),
    ShrinkBundlePlan.absoluteCD i.val (a i) (origin B i)]

/-- RHS expressions at offsets 36 through 39 on the degree refresh. -/
def refreshTerms : Fin 4 → Expr :=
  let s := RefreshBlockPlan.shape B
  let p := RefreshBlockPlan.input (F B) S.steps (0 : Fin 6)
  ![PortRefresh.LevelRecipe.termStart s p,.lit s.stride,.lit 0,.lit 0]

variable {offset N : ℕ}

/-- The address of the selected score bit survives all head publications. -/
theorem shrink_layoutCell_stable (entry : Entry L first pub state original)
    (room : levelStart L (first+i.val)+66 ≤ 2^w) (pitch : (pub 1-1).val < levelStart L (first+i.val)+36)
    (lo : 36 ≤ offset) (hi : offset+N ≤ 54)
    (frame : Agree (PublishedHeads.Outside (levelStart L (first+i.val)+offset) N) mem original) :
    (SelectedPlan.layoutCell (chosen B i)).eval pub state mem = (SelectedPlan.layoutCell (chosen B i)).eval pub state original :=
  (selected_heads B i (readInputs B entry room pitch lo hi frame)).2.2.2

set_option maxHeartbeats 1200000 in
theorem shrink_term_stable (entry : Entry L first pub state original)
    (room : levelStart L (first+i.val)+66 ≤ 2^w) (pitch : (pub 1-1).val < levelStart L (first+i.val)+36)
    (lo : 36 ≤ offset) (hi : offset+N ≤ 54)
    (score : levelStart L (first+i.val)+54 ≤ ((SelectedPlan.layoutCell (chosen B i)).eval pub state original).val)
    (frame : Agree (PublishedHeads.Outside (levelStart L (first+i.val)+offset) N) mem original)
    (j : Fin 4) : (shrinkTerms B i j).eval pub state mem = (shrinkTerms B i j).eval pub state original := by
  have h := readInputs B entry room pitch lo hi frame
  obtain ⟨ht,_,_,hc⟩ := selected_heads B i h
  have hs : same pub state mem original (SelectedPlan.layout (chosen B i)) := by
    change mem ((SelectedPlan.layoutCell _).eval _ _ mem).val = _
    rw [hc]
    exact frame _ (.inr (by omega))
  have hab := (bundle_heads B i h).2.2.2.2.2.2.1
  fin_cases j
  · exact ht
  · rfl
  · exact hs
  · exact hab

set_option maxHeartbeats 1200000 in
theorem shrink_data_stable (entry : Entry L first pub state original)
    (room : levelStart L (first+i.val)+66 ≤ 2^w) (pitch : (pub 1-1).val < levelStart L (first+i.val)+36)
    (lo : 36 ≤ offset) (hi : offset+N ≤ 54)
    (frame : Agree (PublishedHeads.Outside (levelStart L (first+i.val)+offset) N) mem original) (j : Fin 14) :
    let rhs := BlockDataHeads.values B (F B) i (origin B i) (BlockProgram.arena B i.val 1)
      (BlockProgram.arena B i.val 2) (BlockProgram.arena B i.val 3) j
    rhs.eval pub state mem = rhs.eval pub state original := by
  have h := readInputs B entry room pitch lo hi frame
  obtain ⟨owner,ranks,ids,sorted,pref,ab,_,size⟩ := bundle_heads B i h
  obtain ⟨_,dense,role,_⟩ := selected_heads B i h
  obtain ⟨rows,inverse⟩ := slot_heads B i h
  have inter : same pub state mem original (BlockSlices.intervals i (BlockProgram.arena B i.val 2)) := by
    simp only [same,BlockSlices.intervals,slots,sites,eval_add,eval_mul,eval_lit,h.arena,h.vertex,h.deg,h.lane]
  have abHead : same pub state mem original ((ShrinkBundlePlan.abParams i.val (a i) (origin B i)) 4) := by
    change same pub state mem original ((ShrinkBundlePlan.abStart i.val (a i) (origin B i)).add
      (ShrinkBundlePlan.blockSize i.val (a i)))
    simp only [same,eval_add,ab,size]
  fin_cases j
  · exact h.next
  · exact inverse
  · exact inter
  · exact h.arena 1
  · exact owner
  · exact ranks
  · exact ids
  · exact dense
  · exact sorted
  · exact pref
  · exact ab
  · exact abHead
  · exact role
  · exact rows

theorem refresh_term_stable (entry : Entry L first pub state original)
    (room : levelStart L (first+S.steps)+66 ≤ 2^w) (pitch : (pub 1-1).val < levelStart L (first+S.steps)+36)
    (lo : 36 ≤ offset) (hi : offset+N ≤ 54)
    (frame : Agree (PublishedHeads.Outside (levelStart L (first+S.steps)+offset) N) mem original) (j : Fin 4) :
    (refreshTerms B j).eval pub state mem = (refreshTerms B j).eval pub state original := by
  have h := readInputs B entry room pitch lo hi frame
  have head : same pub state mem original (PortRefresh.LevelRecipe.termStart (RefreshBlockPlan.shape B)
      (RefreshBlockPlan.input (F B) S.steps (0 : Fin 6))) := by
    have ar : same pub state mem original (table (F B) S.steps (0 : Fin 6)) := h.arena 0
    simp only [same,PortRefresh.LevelRecipe.termStart,PortRefresh.LevelRecipe.demandStart,PortRefresh.LevelRecipe.blocks,
      PortRefresh.LevelRecipe.segments,PortRefresh.LevelRecipe.sites,RefreshBlockPlan.input,eval_add,eval_mul,eval_lit,
      h.vertex,h.residual,ar]
  fin_cases j <;> first | exact head | rfl

theorem next_level_stable {step : ℕ} (entry : Entry L first pub state original)
    (pitch : (pub 1-1).val < levelStart L (first+step)+36) (lo : 36 ≤ offset)
    (frame : Agree (PublishedHeads.Outside (levelStart L (first+step)+offset) N) mem original) :
    (atLevel (step+1)).eval pub state mem = (atLevel (step+1)).eval pub state original := by
  have afterEntry : Entry L first pub state mem :=
    ⟨entry.pointer,(frame _ (.inl (pitch.trans_le (Nat.add_le_add_left lo _)))).trans entry.pitch⟩
  exact (eval_atLevel afterEntry (step+1)).trans (eval_atLevel entry (step+1)).symm

end CompressorRecords.BlockHeadStability

end

end VPVNP
end Computability
end OAI
