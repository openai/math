import OAI.Computability.VPVNP.CompressorRefreshCoreHeader
import OAI.Computability.VPVNP.CompressorBlockGroups
import OAI.Computability.VPVNP.CompressorWindowPrepared
import OAI.Computability.VPVNP.CompressorRecordsCopyIncidence

/-!
# Planner operands of the six native refresh column copies

The input header supplies the old vertex count, residual lanes and scratch origin.
The output header supplies each canonical destination pointer. The first three scans
copy one word per promoted base port and the last three copy one word per actual slot.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.RefreshCopyHeader

open BurstRAM Compression DescriptorSpace PhaseRecipe BlockPlanner Schedule
open PortRefresh LevelRecipe NewSlots
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {g w : ℕ} (X : State S.portExponent (S.portExponent + g))
  (Y : State (S.degreeExponent 0) g)
variable (start : ℕ) (old : IncidenceDirectory w)

local notation "geom" => BlockProgram.geometry B
local notation "shapeR" => RefreshBlockPlan.shape B
local notation "inputR" => RefreshBlockPlan.input geom S.steps (0 : Fin 6)
local notation "P" => Allocation.plan X (LevelRecipe.Shape.a₀ shapeR) (LevelRecipe.Shape.dH shapeR)
  (LevelRecipe.Shape.ties shapeR) (LevelRecipe.Shape.stride shapeR) start
local notation "visit" => RefreshBlockPlan.copyColumn B geom S.steps inputR

private theorem column_reads {s : LevelRecipe.Shape} {I : Input} {C : Context w} {D : ℕ → Prop}
    (h : InputReads D C.pub C.state C.memory I) (i : Fin 6) :
    (column s I i).ReadsFrom D C.pub C.state C.memory := by
  let R := Expr.ReadsFrom D C.pub C.state C.memory
  have ps : R (sites s I) := ⟨⟨h.vertices, trivial⟩, h.lanes⟩
  have bl : R (blocks I) := ⟨h.vertices, h.lanes⟩
  have dem : R (demandStart s I) := ⟨h.start, trivial, ps, trivial⟩
  have term : R (termStart s I) := ⟨dem, bl, trivial⟩
  have sup : R (supplyStart s I) := ⟨term, bl, trivial⟩
  have target : R (targetPort s I) := ⟨sup, ps, trivial⟩
  have rev : R (reverseSlot s I) := ⟨target, trivial, trivial⟩
  exact ⟨⟨rev, trivial, trivial⟩, trivial, ps, trivial⟩

variable {L : Layout} {first rows : ℕ} (C : Context w)
local notation "next" => first + (S.steps + 1)
local notation "U" => packedIncidence L w (next) rows

/-- Stop and parameter words at the actual copy visit. The count equalities identify
its two scan lengths with those of the refreshed state. -/
theorem eval (entry : LevelFields.Entry L first C.pub C.state C.memory)
    (header : RefreshCore.Header (Fintype.card X.Base) g (levelStart L (first + S.steps))
      start old C.memory)
    (successor : TraversalHeaders.HeadBank L (next) rows C.memory)
    (fields : L.shape.scalarFields = 54)
    (room : levelStart L (next) + 59 < 2 ^ w)
    (baseCount : Fintype.card Y.Base = Fintype.card X.Base * 2 ^ S.portExponent)
    (actualCount : Y.positions * 2 ^ (S.degreeExponent 0) = (P).capacity) (c : Fin 6) :
    C.eval ((visit c).stop) = word (CopyIncidence.rows Y c) ∧
      ∀ j : Fin 3, C.eval ((visit c).params j) =
        CopyIncidence.copyPublic (((P).output w).column c) ((U).column c) j := by
  have data : Describes (s := shapeR) inputR C X start old :=
    RefreshCore.Header.describes (F := geom) rfl (0 : Fin 6) rfl entry header
  have h := addresses (s := shapeR) inputR C X start old data
  have dest : C.eval (LevelFields.incidence geom (S.steps + 1) c) = (U).column c := by
    rw [packed_column]
    have read := LevelFields.eval_scalar entry (S.steps + 1) (54 + c.val) (by have := c.isLt; omega)
    exact read.trans (by
      simpa only [incidenceHead, fields, Nat.add_assoc] using successor.incidence c)
  constructor
  · change C.eval (RefreshBlockPlan.columnCount B inputR c) = _
    by_cases small : c.val < 3
    · simp only [RefreshBlockPlan.columnCount,CopyIncidence.rows,small,↓reduceIte,baseCount]
      exact (counters (s := shapeR) inputR C X start old data (.base : Stage shapeR)).2
    · simp only [RefreshBlockPlan.columnCount,CopyIncidence.rows,small,↓reduceIte,actualCount]
      exact h.capacity_eq
  · intro j
    fin_cases j
    · rfl
    · exact h.column_eq c
    · exact dest

/-- Support in a general preserved memory region follows from the old header cells,
the new pointer cells, and the single pitch read. -/
theorem reads {D : ℕ → Prop} (entry : LevelFields.Entry L first C.pub C.state C.memory)
    {V : ℕ} (header : RefreshCore.Header V g (levelStart L (first + S.steps))
      start old C.memory)
    (room : levelStart L (next) + 59 < 2 ^ w) (pitch : D (C.pub 1 - 1).val)
    (oldCells : ∀ n ≤ 60, D (levelStart L (first + S.steps) + n))
    (newCells : ∀ c : Fin 6, D (levelStart L (next) + (54 + c.val))) (c : Fin 6) :
    HeaderOperands.Supported D C.pub C.state C.memory (visit c) := by
  have data : InputReads D C.pub C.state C.memory inputR :=
    RefreshCore.Header.reads (F := geom) rfl (0 : Fin 6) rfl entry header pitch oldCells
  refine ⟨trivial, ?_, ?_⟩
  · change (RefreshBlockPlan.columnCount B inputR c).ReadsFrom D C.pub C.state C.memory
    unfold RefreshBlockPlan.columnCount
    split
    · exact ⟨⟨data.vertices, trivial⟩, trivial⟩
    · exact ⟨⟨⟨data.vertices, trivial⟩, data.lanes⟩, trivial⟩
  · intro j
    fin_cases j
    · trivial
    · exact column_reads (C := C) data c
    · exact GreedyVisit.scalar_support D L first (S.steps + 1) (54 + c.val) entry pitch
        (newCells c) (by have := c.isLt; omega)

section Physical

variable (base : Word w) (positions blocks t : ℕ)
local notation "scr" => BlockProgram.script B
local notation "lay" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "pub" => Schedule.Ports.data pt
local notation "idx" => Script.levelsPerBlock scr * t
local notation "st" => (levelStart lay (idx) : Word w)
local notation "succIdx" => (idx) + (S.steps + 1)
local notation "dest" => packedIncidence lay w (succIdx) rows

/-- The six installed scans use the native parameters and only read cells permitted
by the physical calendar. The old and new publications are read at this visit's memory. -/
theorem operands (m : Memory w)
    (header : RefreshCore.Header (Fintype.card X.Base) g (levelStart lay ((idx) + S.steps))
      start old m)
    (successor : TraversalHeaders.HeadBank lay (succIdx) rows m)
    (pitch : m (pub 1 - 1).val = (levelWords lay : Word w)) (live : t < blocks)
    (fit : endAddress lay < 2 ^ w)
    (baseCount : Fintype.card Y.Base = Fintype.card X.Base * 2 ^ S.portExponent)
    (actualCount : Y.positions * 2 ^ (S.degreeExponent 0) = (P).capacity) (c : Fin 6) :
    (visit c).stop.eval pub st m = word (CopyIncidence.rows Y c) ∧
      (∀ j : Fin 3, ((visit c).params j).eval pub st m =
        CopyIncidence.copyPublic (((P).output w).column c) ((dest).column c) j) ∧
      HeaderOperands.Supported (Window.operandRegion scr lay base) pub st m (visit c) := by
  have liveNext : succIdx < (lay).levels := by
    have bound := Nat.mul_le_mul_left (S.steps + 1) live
    change (S.steps + 1) * t + (S.steps + 1) < 1 + (S.steps + 1) * blocks
    rw [Nat.mul_succ] at bound; omega
  have room : levelStart lay (succIdx) + 59 < 2 ^ w := by
    have h := DescriptorSpace.level_room lay fit ⟨succIdx, liveNext⟩
    change levelStart lay ((succIdx) + 1) < 2 ^ w at h
    have size : levelHeaderWords lay = 66 := rfl
    simp only [levelStart, Nat.succ_mul, levelWords, size] at h ⊢; omega
  let C : Context w := ⟨pub, st, m⟩
  have entry : LevelFields.Entry lay (idx) C.pub C.state C.memory := ⟨rfl, pitch⟩
  obtain ⟨stop, params⟩ :=
    eval B X Y start old C entry header successor rfl room baseCount actualCount c
  refine ⟨stop, params, reads B start old C entry header room (Or.inr (Or.inl rfl)) ?_ ?_ c⟩
  · intro n _
    exact Or.inr (Or.inr ((levelStart_mono lay (Nat.zero_le _)).trans (Nat.le_add_right ..)))
  · intro j
    exact Or.inr (Or.inr ((levelStart_mono lay (Nat.zero_le _)).trans (Nat.le_add_right ..)))

end Physical
end CompressorRecords.RefreshCopyHeader

end

end VPVNP
end Computability
end OAI
