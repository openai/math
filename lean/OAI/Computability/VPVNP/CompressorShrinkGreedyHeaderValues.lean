import OAI.Computability.VPVNP.CompressorShrinkHeaderReads
import OAI.Computability.VPVNP.CompressorShrinkHistoryDirectory
import OAI.Computability.VPVNP.CompressorBlockHeaderRun
import OAI.Computability.VPVNP.CompressorGreedyPlannerFootprint

/-!
# The greedy workers' physical input header after a shrinking substep

The three header calls publish the selected input scalars, initialize the
next level and publish its array heads. The old incidence heads, table-zero
pointer and pitch lie outside those writes. All fields used by the shrinking
planner lie strictly below its first scratch address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkGreedyHeaderValues

open BurstRAM Compression DescriptorSpace BlockHeaderRun ShrinkBlockInputs
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
  (B : S.Templates) (i : Fin S.steps) {w g : ℕ} (X : State (a i) (packingLaneBits (a i) g))
  (T : IncidenceDirectory w)

/-- The memory certificate can be transported through every native greedy
visit using only the write bound at the start of the scratch allocation. -/
structure Header (L : Layout) (first start : ℕ) (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) : Prop where
  raw : ShrinkHeaderReads.Header i X T start L first m
  entry : LevelFields.Entry L first pub st m
  fieldsBelow : levelStart L (first+i.val)+60 < start
  pitchBelow : (pub 1-1).val < start
  strideFits : levelWords L < 2^w

variable {i X T} {L : Layout} {first start : ℕ} {pub : Fin 5 → Word w} {st : Word w}
  {m m' : Memory w}

theorem Header.keep_below (h : Header i X T L first start pub st m)
    (same : ∀ x < start, m' x = m x) : Header i X T L first start pub st m' :=
  ⟨h.raw.keep_below h.fieldsBelow same, ⟨h.entry.pointer,(same _ h.pitchBelow).trans h.entry.pitch⟩,
    h.fieldsBelow,h.pitchBelow,h.strideFits⟩

theorem Header.reads_at (h : Header i X T L first start pub st m)
    (same : ∀ x < start, m' x = m x) :
    GreedyLevelPlan.Reads (BlockProgram.geometry B) i.val (a i) (BlockProgram.arena B i.val 0)
      pub st m' (Fintype.card X.Base) g start T := by
  have h' := h.keep_below same
  exact (ShrinkHeaderReads.Header.reads B h'.raw h'.entry).1

variable (f : B.Entry → R) (hf : B.IsSolution f) (i X) (sel : SelectedScore.Selection B X)
  (tape : List Bool) (base : Word w) (positions blocks : ℕ)
local notation "lay" => BlockProgram.layout B base.val positions blocks
local notation "v" => PairSimulation.TraversalRows.shrinkLevel B f hf i X sel tape

/-- Read the actual old heads through the relabel/advance/publication call
sequence, using its published input fields and its three write intervals. -/
theorem post_header (T : IncidenceDirectory w) (first : ℕ) (old new : Fin (lay).levels)
    (hOld : old.val = first+i.val) (hNew : new.val = old.val+1) (m : Memory w)
    (run : Substep v lay old new (by change 6 ≤ 54; decide) m)
    (fit : endAddress lay < 2^w) (pub : Fin 5 → Word w) (st : Word w)
    (entry : LevelFields.Entry lay first pub st m) (pitch : (pub 1-1).val < levelStart lay old)
    (heads : ∀ c : Fin 6, m (incidenceHead lay old c) = T.column c)
    (scratch : m (tableHead lay old (0 : Fin 6)) = (tableBase lay old (0 : Fin 6) : Word w)) :
    Header i X T lay first (tableBase lay old (0 : Fin 6)) pub st (finalMemory v lay old new m) := by
  let here := levelStart lay old
  let next := levelStart lay new
  let post := finalMemory v lay old new m
  have sz : (lay).shape.scalarFields = 54 := rfl
  have ts : (lay).shape.tables = 6 := rfl
  have words : 66 ≤ levelWords lay := by simp only [levelWords,levelHeaderWords,sz,ts]; omega
  have step : next = here+levelWords lay := by simp [here,next,hNew,levelStart,Nat.succ_mul,Nat.add_assoc]
  have fitNext : next < 2^w := by
    change levelStart lay new < _; rw [hNew]; exact level_room lay fit old
  have room : here+60 < 2^w := by omega
  have fieldBelow : here+60 < tableBase lay old (0 : Fin 6) := by
    simp only [tableBase,arrayBase,incidenceStart,levelHeaderWords,sz,ts,Fin.val_zero,Nat.zero_mul,Nat.add_zero]
    change here+60 < here+66+6*slotCapacity lay
    omega
  have keep (j : ℕ) (lo : 6 ≤ j) (hi : j ≤ 60) : post (here+j) = m (here+j) := by
    apply run.outside
    · right; change here+6 ≤ here+j; omega
    · left; change here+j < next; omega
    · left; change here+j < next+(lay).shape.scalarFields; omega
  have hpitch : post (pub 1-1).val = m (pub 1-1).val := by
    change (pub 1-1).val < here at pitch
    apply run.outside
    · exact .inl pitch
    · left; change (pub 1-1).val < next; omega
    · left; change (pub 1-1).val < next+(lay).shape.scalarFields; omega
  refine ⟨?_,⟨entry.pointer,hpitch.trans entry.pitch⟩,hOld ▸ fieldBelow,?_,by omega⟩
  · have now := run.input
    refine ⟨hOld ▸ room,hOld ▸ now.vertices,hOld ▸ now.degree,hOld ▸ now.lanes,
      hOld ▸ now.residual,?_,?_⟩
    · intro c
      rw [← hOld]
      apply (keep (54+c.val) (by omega) (by have := c.isLt; omega)).trans
      simpa only [incidenceHead,sz,here,Nat.add_assoc] using heads c
    · rw [← hOld]
      apply (keep 60 (by decide) le_rfl).trans
      simpa only [tableHead,sz,Fin.val_zero,Nat.add_zero,Nat.add_assoc] using scratch
  · change (pub 1-1).val < here at pitch
    omega

end CompressorRecords.ShrinkGreedyHeaderValues

end VPVNP
end Computability
end OAI
