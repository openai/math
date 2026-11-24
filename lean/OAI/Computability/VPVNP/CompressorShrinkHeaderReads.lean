import OAI.Computability.VPVNP.CompressorBlockProgram
import OAI.Computability.VPVNP.CompressorSourceCalendarEntry

/-!
# Published level fields read by the shrinking calendar recipes

The old site, degree and residual-lane counts, the six incidence heads
and the first scratch pointer are read from the actual level header.
Agreement on the shared data region transports these values through the
scheduler's launch.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkHeaderReads

open BurstRAM BlockPlanner Compression DescriptorSpace ShrinkBlockInputs SourceTransport
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w) (start : ℕ)
variable (L : Layout) (first : ℕ)

local notation "here" => levelStart L (first+i.val)

/-- Only the fields actually used by the term planner are specified. -/
structure Header (mem : Memory w) : Prop where
  room : here+60 < 2^w
  vertices : mem (here+0) = (Fintype.card X.Base : Word w)
  degree : mem (here+1) = ((2^(a i) : ℕ) : Word w)
  lanes : mem (here+2) = ((2^(packingLaneBits (a i) g) : ℕ) : Word w)
  residual : mem (here+3) = ((2^g : ℕ) : Word w)
  incidence : ∀ c : Fin 6, mem (here+(54+c.val)) = T.column c
  scratch : mem (here+60) = (start : Word w)

variable {i X T start L first}

theorem Header.keep {before after : Memory w} (h : Header i X T start L first before)
    (same : Agree (levelStart L 0 ≤ ·) before after) : Header i X T start L first after := by
  have lo : levelStart L 0 ≤ here := levelStart_mono L (Nat.zero_le _)
  have field (n : ℕ) : after (here+n) = before (here+n) := (same _ (by omega)).symm
  exact ⟨h.room,(field 0).trans h.vertices,(field 1).trans h.degree,(field 2).trans h.lanes,
    (field 3).trans h.residual,fun c => (field _).trans (h.incidence c),(field 60).trans h.scratch⟩

theorem Header.keep_below {before after : Memory w} (h : Header i X T start L first before)
    (below : here+60 < start) (same : ∀ addr < start, after addr = before addr) :
    Header i X T start L first after := by
  have field (n : ℕ) (hn : n ≤ 60) : after (here+n) = before (here+n) := same _ (by omega)
  exact ⟨h.room,(field 0 (by decide)).trans h.vertices,(field 1 (by decide)).trans h.degree,
    (field 2 (by decide)).trans h.lanes,(field 3 (by decide)).trans h.residual,
    fun c => (field _ (by have := c.isLt; omega)).trans (h.incidence c),(field 60 le_rfl).trans h.scratch⟩

theorem Header.reads {pub : Fin 5 → Word w} {state : Word w} {mem : Memory w}
    (h : Header i X T start L first mem) (entry : LevelFields.Entry L first pub state mem) :
    ShrinkBundlePlan.Reads X (BlockProgram.geometry B) i.val (BlockProgram.arena B i.val 0) pub state mem start T := by
  have cell (offset : ℕ) (hoff : offset ≤ 60) :
      (LevelFields.scalar i.val offset).eval pub state mem = mem (here+offset) :=
    LevelFields.eval_scalar entry i.val offset ((Nat.add_le_add_left hoff _).trans_lt h.room)
  refine ⟨⟨(cell 0 (by decide)).trans h.vertices,(cell 1 (by decide)).trans h.degree,
    (cell 3 (by decide)).trans h.residual,fun c => ?_,(cell 60 le_rfl).trans h.scratch⟩,
    (cell 2 (by decide)).trans h.lanes⟩
  exact (cell (54+c.val) (by have := c.isLt; omega)).trans (h.incidence c)

end CompressorRecords.ShrinkHeaderReads

end

end VPVNP
end Computability
end OAI
