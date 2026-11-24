import OAI.Computability.VPVNP.CompressorBlockHeadStability
import OAI.Computability.VPVNP.CompressorWindowPrepared
import OAI.Computability.VPVNP.CompressorHeaderOperands

/-!
# Read footprints of the shrinking and refresh head formulas

The online recipe can read its pitch and the graph data suffix. The four
level scalars and six table pointers lie in that suffix, as does the
selected shrinking layout bit. Arithmetic on these operands makes no
additional external reads.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockHeadReads

open BurstRAM BurstRAM.PrivateRAM DescriptorSpace PhaseRecipe Schedule BlockPlanner Compression LevelFields
open scoped Fin.CommRing
open private recordsEnd firstRecord from OAI.Computability.VPVNP.CompressorGreedyLevelPlan

variable {w : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {A : Script} {L : Layout} {base state : Word w} {m : Memory w} {first : ℕ}

local notation "pt" => Workspace.ports (arity A.catalog) base
local notation "pub" => Schedule.Ports.data pt
local notation "D" => Window.operandRegion A L base
local notation "read" => Expr.ReadsFrom D pub state m
local notation "H" => levelStart L 0

private theorem add_reads {w : ℕ} (d : ℕ → Prop) (p : Fin 5 → Word w) (s : Word w) (mem : Memory w)
    (x y : Expr) : (x.add y).ReadsFrom d p s mem ↔ x.ReadsFrom d p s mem ∧ y.ReadsFrom d p s mem := Iff.rfl

private theorem mul_reads {w : ℕ} (d : ℕ → Prop) (p : Fin 5 → Word w) (s : Word w) (mem : Memory w)
    (x y : Expr) : (x.mul y).ReadsFrom d p s mem ↔ x.ReadsFrom d p s mem ∧ y.ReadsFrom d p s mem := Iff.rfl

private theorem lit_reads {w : ℕ} (d : ℕ → Prop) (p : Fin 5 → Word w) (s : Word w) (mem : Memory w) (n : ℕ) :
    (Expr.lit n).ReadsFrom d p s mem := trivial

/-- Level arithmetic reads the physical pitch cell allowed by the calendar. -/
theorem level (step : ℕ) : read (atLevel step) :=
  ⟨trivial,trivial,⟨trivial,trivial⟩,Or.inr (Or.inl rfl)⟩

theorem address (step off : ℕ) : read (LevelFields.address step off) := ⟨level step,trivial⟩

private theorem field {step : ℕ} (entry : Entry L first pub state m) (room : levelStart L (first+step)+66 ≤ 2^w)
    (j : ℕ) (small : j < 66) : read (scalar step j) := by
  refine ⟨address step j,Or.inr (Or.inr ?_)⟩
  rw [eval_address entry,Fin.val_natCast,Nat.mod_eq_of_lt ((Nat.add_lt_add_left small _).trans_le room)]
  exact (levelStart_mono L (Nat.zero_le _)).trans (Nat.le_add_right ..)

private structure Inputs (step : ℕ) (d : ℕ → Prop) (p : Fin 5 → Word w) (s : Word w) (mem : Memory w) : Prop where
  vertex : (vertices step).ReadsFrom d p s mem
  deg : (degree step).ReadsFrom d p s mem
  lane : (lanes step).ReadsFrom d p s mem
  residual : (residualLanes step).ReadsFrom d p s mem
  arena (j : Fin 6) : (BlockProgram.arena B step j).ReadsFrom d p s mem

private theorem inputs {step : ℕ} (entry : Entry L first pub state m) (room : levelStart L (first+step)+66 ≤ 2^w) :
    Inputs B step D pub state m :=
  ⟨field entry room 0 (by decide),field entry room 1 (by decide),field entry room 2 (by decide),
    field entry room 3 (by decide),fun j => field entry room (54+6+j.val) (by have := j.isLt; omega)⟩

variable (i : Fin S.steps)

local notation "st" => i.val
local notation "a" => ShrinkBlockInputs.a i
local notation "F" => BlockProgram.geometry B
local notation "o" => BlockProgram.arena B st 0
local notation "c" => ShrinkBlockInputs.selectedInputs B F i o

section Core

variable {d : ℕ → Prop} {p : Fin 5 → Word w}
local notation "reads" => Expr.ReadsFrom d p state m

private theorem bundle_heads (h : Inputs B st d p state m) :
    reads (ShrinkBundlePlan.owner st a o) ∧ reads (ShrinkBundlePlan.ranks st a o) ∧
    reads (ShrinkBundlePlan.ids st a o) ∧ reads (ShrinkBundlePlan.sorted st a o) ∧
    reads (ShrinkBundlePlan.prefixStart st a o) ∧ reads (ShrinkBundlePlan.abStart st a o) ∧
    reads (ShrinkBundlePlan.absoluteCD st a o) ∧ reads (ShrinkBundlePlan.blockSize st a) := by
  simp only [ShrinkBundlePlan.absoluteCD,ShrinkBundlePlan.prefixStart,ShrinkBundlePlan.abStart,
    ShrinkBundlePlan.totalStart,ShrinkBundlePlan.sorted,ShrinkBundlePlan.ranks,ShrinkBundlePlan.gathered,
    ShrinkBundlePlan.ids,ShrinkBundlePlan.counts,ShrinkBundlePlan.owner,ShrinkBundlePlan.preliminary,
    ShrinkBundlePlan.rectangle,ShrinkBundlePlan.bucketCount,ShrinkBundlePlan.blockSize,ShrinkBundlePlan.bundles,
    GreedyLevelPlan.greedyStop,GreedyLevelPlan.zeroAddress,GreedyLevelPlan.shiftBase,GreedyLevelPlan.offsetBase,
    recordsEnd,firstRecord,LevelFields.sites,LevelFields.slots,add_reads,mul_reads,lit_reads,h.arena,h.vertex,h.deg,h.lane,h.residual,and_self]

private theorem selected_heads (h : Inputs B st d p state m) :
    reads (c).termBase ∧ reads (ShrinkTermRecipe.dense a (ShrinkBundlePlan.termInputs st a o)) ∧
    reads (SelectedPlan.roleBase c) ∧ reads (SelectedPlan.layoutCell c) ∧ reads (c).newSites ∧ reads (c).motifs := by
  have hab := (bundle_heads B i h).2.2.2.2.2.1
  simp only [ShrinkBlockInputs.selectedInputs,ShrinkBlockInputs.newSites,SelectedPlan.roleBase,SelectedPlan.placementBase,
    SelectedPlan.layoutCell,SelectedPlan.scoreBase,ShrinkTermRecipe.term,ShrinkTermRecipe.dense,ShrinkTermRecipe.count,
    ShrinkTermRecipe.bundles,ShrinkBundlePlan.termInputs,LevelFields.sites,add_reads,mul_reads,lit_reads,
    h.vertex,h.deg,h.lane,h.residual,hab,and_self]

private theorem slot_heads (h : Inputs B st d p state m) :
    let z := SlotLevel.Recipe.counts (ShrinkBlockInputs.slotTemplate i)
      (ShrinkBlockInputs.slotInputs B F i o (BlockProgram.arena B st 3))
    reads z.rows ∧ reads z.inverse := by
  simp only [SlotLevel.Recipe.counts,ShrinkBlockInputs.slotInputs,ShrinkBlockInputs.newSites,
    add_reads,mul_reads,lit_reads,h.arena,h.vertex,h.residual,and_self]

end Core

/-- The same operand proof applies to a smaller region preserved by the
preceding calls. Only the pitch, four scalars, six table heads and the chosen
layout bit need to be available in that region. -/
theorem resident_operands_of (d : ℕ → Prop) {p : Fin 5 → Word w} (entry : Entry L first p state m)
    (room : levelStart L (first+st)+66 ≤ 2^w) (pitch : d (p 1-1).val)
    (scalars : ∀ j : Fin 4, d (levelStart L (first+st)+j.val))
    (tables : ∀ j : Fin 6, d (levelStart L (first+st)+(60+j.val)))
    (score : d ((SelectedPlan.layoutCell c).eval p state m).val) :
    let reads := Expr.ReadsFrom d p state m
    reads (c).newSites ∧ reads (c).motifs ∧ reads (BlockProgram.arena B st 5) ∧ reads (SelectedPlan.roleBase c) ∧
    reads (SelectedPlan.layout c) ∧ reads (ShrinkBundlePlan.absoluteCD st a o) ∧ reads (atLevel st) := by
  have lev : (atLevel st).ReadsFrom d p state m := ⟨trivial,trivial,⟨trivial,trivial⟩,pitch⟩
  have cell (j : ℕ) (small : j < 66) (atCell : d (levelStart L (first+st)+j)) :
      (scalar st j).ReadsFrom d p state m := by
    refine ⟨⟨lev,trivial⟩,?_⟩
    rw [eval_address entry,Fin.val_natCast,Nat.mod_eq_of_lt ((Nat.add_lt_add_left small _).trans_le room)]
    exact atCell
  have h : Inputs B st d p state m :=
    ⟨cell 0 (by decide) (scalars 0),cell 1 (by decide) (scalars 1),cell 2 (by decide) (scalars 2),
      cell 3 (by decide) (scalars 3),fun j => cell (60+j.val) (by have := j.isLt; omega) (tables j)⟩
  obtain ⟨_,_,roles,layoutAddress,newSites,motifs⟩ := selected_heads B i h
  exact ⟨newSites,motifs,h.arena 5,roles,⟨layoutAddress,score⟩,(bundle_heads B i h).2.2.2.2.2.2.1,lev⟩

/-- All seven inputs shared by the hidden and map resident windows. -/
theorem resident_operands (entry : Entry L first pub state m) (room : levelStart L (first+st)+66 ≤ 2^w)
    (score : H ≤ ((SelectedPlan.layoutCell c).eval pub state m).val) :
    read (c).newSites ∧ read (c).motifs ∧ read (BlockProgram.arena B st 5) ∧ read (SelectedPlan.roleBase c) ∧
    read (SelectedPlan.layout c) ∧ read (ShrinkBundlePlan.absoluteCD st a o) ∧ read (atLevel st) := by
  have h := inputs B entry room
  obtain ⟨_,_,roles,cell,newSites,motifs⟩ := selected_heads B i h
  exact ⟨newSites,motifs,h.arena 5,roles,⟨cell,Or.inr (Or.inr score)⟩,
    (bundle_heads B i h).2.2.2.2.2.2.1,level st⟩

theorem shrink_terms (entry : Entry L first pub state m) (room : levelStart L (first+st)+66 ≤ 2^w)
    (score : H ≤ ((SelectedPlan.layoutCell c).eval pub state m).val) (j : Fin 4) :
    read (BlockHeadStability.shrinkTerms B i j) := by
  have h := inputs B entry room
  obtain ⟨term,_,_,cell,_,_⟩ := selected_heads B i h
  fin_cases j
  · exact term
  · trivial
  · exact ⟨cell,Or.inr (Or.inr score)⟩
  · exact (bundle_heads B i h).2.2.2.2.2.2.1

theorem shrink_data (entry : Entry L first pub state m) (room : levelStart L (first+st)+66 ≤ 2^w) (j : Fin 14) :
    read (BlockDataHeads.values B F i o (BlockProgram.arena B st 1) (BlockProgram.arena B st 2)
      (BlockProgram.arena B st 3) j) := by
  have h := inputs B entry room
  obtain ⟨owner,ranks,ids,sorted,pref,ab,_,size⟩ := bundle_heads B i h
  obtain ⟨_,dense,role,_,_,_⟩ := selected_heads B i h
  obtain ⟨rows,inverse⟩ := slot_heads B i h
  fin_cases j
  · exact level (st+1)
  · exact inverse
  · exact ⟨h.arena 2,⟨trivial,⟨⟨h.vertex,h.lane⟩,h.deg⟩⟩,trivial⟩
  · exact h.arena 1
  · exact owner
  · exact ranks
  · exact ids
  · exact dense
  · exact sorted
  · exact pref
  · exact ab
  · exact ⟨ab,size⟩
  · exact role
  · exact rows

theorem refresh_terms (entry : Entry L first pub state m) (room : levelStart L (first+S.steps)+66 ≤ 2^w) (j : Fin 4) :
    read (BlockHeadStability.refreshTerms B j) := by
  have h := inputs B entry room
  fin_cases j
  · have arena : read (table F S.steps (0 : Fin 6)) := h.arena 0
    change read (PortRefresh.LevelRecipe.termStart (RefreshBlockPlan.shape B)
      (RefreshBlockPlan.input F S.steps (0 : Fin 6)))
    simp only [PortRefresh.LevelRecipe.termStart,PortRefresh.LevelRecipe.demandStart,PortRefresh.LevelRecipe.blocks,
      PortRefresh.LevelRecipe.segments,PortRefresh.LevelRecipe.sites,RefreshBlockPlan.input,add_reads,mul_reads,lit_reads,
      h.vertex,h.residual,arena,and_self]
  all_goals trivial

/-- All operands of the two-word one-shot publisher use the same allowed region. -/
theorem publish_supported {dest value : Expr} (hd : read dest) (hv : read value) :
    HeaderOperands.Supported D pub state m (publish dest value) := by
  refine ⟨trivial,trivial,?_⟩
  intro j
  fin_cases j
  · exact hd
  · exact hv

end CompressorRecords.BlockHeadReads

end

end VPVNP
end Computability
end OAI
