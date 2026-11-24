import OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe
import OAI.Computability.VPVNP.CompressorDescriptorSpace
import OAI.Computability.VPVNP.CompressorLevelCounts
import OAI.Computability.VPVNP.CompressorRecordsLevelCalendar

/-!
# Physical header operands for online compressor recipes

Each recipe enters at the first level of its block. A fixed substep offset
and the runtime level stride select the input or output header. Scalar,
incidence, and scratch-array operands use the published pointer cells. The
directory holds exactly the rows visited by the calendar, which may occupy
less space than the polynomial bound reserved in the capacity calculation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.LevelFields

open BurstRAM BurstRAM.PrivateRAM Compression PhaseRecipe DescriptorSpace
open scoped Fin.CommRing

variable {w : ℕ}

/-- Recipe expression that loads the level-header stride from the cell immediately preceding
the directory. -/
def stride := Expr.load ((Expr.publicWord 1).sub (.lit 1))
/-- Address expression for the header a fixed number of level strides after the block's entry
state. -/
def atLevel (step : ℕ) := Expr.state.add ((Expr.lit step).mul stride)
/-- Address of a field at the specified offset in a header selected relative to the block's
first level. -/
def address (step offset : ℕ) := (atLevel step).add (.lit offset)
/-- Recipe expression that loads one word from the selected level header. -/
def scalar (step offset : ℕ) := Expr.load (address step offset)
/-- Load the published pointer to one of the six incidence columns following the level's scalar
fields. -/
def incidence (shape : Shape) (step : ℕ) (c : Fin 6) := scalar step (shape.scalarFields+c.val)
/-- Load a table's published base pointer from the level header after the six incidence
pointers. -/
def table (shape : Shape) (step : ℕ) (j : Fin shape.tables) := scalar step
    (shape.scalarFields+6+j.val)

/-- Read the number of input base vertices from scalar zero of the selected level. -/
def vertices (step : ℕ) := scalar step 0
/-- Read the input slot degree from scalar one of the selected level. -/
def degree (step : ℕ) := scalar step 1
/-- Read the number of input lanes per base vertex from scalar two of the selected level. -/
def lanes (step : ℕ) := scalar step 2
/-- Read the number of residual lanes from scalar three of the selected level. -/
def residualLanes (step : ℕ) := scalar step 3
/-- Read the next level's slot degree from scalar four of the current level. -/
def nextDegree (step : ℕ) := scalar step 4
/-- Read the refresh expander's degree from scalar five of the selected level. -/
def expanderDegree (step : ℕ) := scalar step 5
/-- Compute the level's input site count by multiplying the base-vertex count by the lanes per
vertex. -/
def sites (step : ℕ) := (vertices step).mul (lanes step)
/-- Compute the number of input ports visited in a level by multiplying its site count by its
slot degree. -/
def slots (step : ℕ) := (sites step).mul (degree step)

/-- Runtime metadata identifying the first level in this block. -/
structure Entry (L : DescriptorSpace.Layout) (first : ℕ) (pub : Fin 5 → Word w)
    (state : Word w) (m : Memory w) : Prop where
  pointer : state = ((levelStart L) first : Word w)
  pitch : m (pub 1-1).val = ((levelWords L) : Word w)

variable {L : DescriptorSpace.Layout} {first : ℕ} {pub : Fin 5 → Word w} {state : Word w}
    {m : Memory w}

theorem eval_stride (e : Entry L first pub state m) : stride.eval pub state m = ((levelWords L)
    : Word w) :=
  e.pitch

theorem eval_atLevel (e : Entry L first pub state m) (step : ℕ) :
    (atLevel step).eval pub state m = ((levelStart L) (first+step) : Word w) := by
  change state + (step : Word w) * stride.eval pub state m = _
  rw [eval_stride e,e.pointer]
  simp [levelStart, Nat.add_mul, add_assoc]

theorem eval_address (e : Entry L first pub state m) (step offset : ℕ) :
    (address step offset).eval pub state m = ((levelStart L) (first+step)+offset : ℕ) := by
  change (atLevel step).eval pub state m + (offset : Word w) = _
  rw [eval_atLevel e]; simp

theorem eval_scalar (e : Entry L first pub state m) (step offset : ℕ)
    (room : (levelStart L) (first + step) + offset < 2 ^ w) :
    (scalar step offset).eval pub state m = m ((levelStart L) (first+step)+offset) := by
  change m ((address step offset).eval pub state m).val = _
  rw [eval_address e, Fin.val_natCast, Nat.mod_eq_of_lt room]

theorem eval_incidence (e : Entry L first pub state m) (step : ℕ) (c : Fin 6)
    (room : (incidenceHead L) (first + step) c < 2 ^ w) :
    (incidence L.shape step c).eval pub state m = m ((incidenceHead L) (first+step) c) := by
  simpa only [incidence,incidenceHead,Nat.add_assoc] using eval_scalar e step
    (L.shape.scalarFields+c.val)
    (by simpa only [incidenceHead,Nat.add_assoc] using room)

theorem eval_table (e : Entry L first pub state m) (step : ℕ) (j : Fin L.shape.tables)
    (room : (tableHead L) (first + step) j < 2 ^ w) :
    (table L.shape step j).eval pub state m = m ((tableHead L) (first+step) j) := by
  simpa only [table,tableHead,Nat.add_assoc] using eval_scalar e step (L.shape.scalarFields+6+j.val)
    (by simpa only [tableHead,Nat.add_assoc] using room)

theorem eval_calendar_entry {d : ℕ} (A : Schedule.LevelCalendar.Calendar d) (pub : Fin 5 → Word w)
    (m : Memory w) (L : DescriptorSpace.Layout)
    (dir : pub 1 = ((directoryBase L) : Word w)) (pitch : A.rowPitch = L.shape.arity + 3)
    (total : m (pub 3).val = ((directoryRows L) : Word w))
    (strideEq : m (pub 1 - 1).val = ((levelWords L) : Word w)) :
    Entry L (A.levelsPerBlock*A.level (m (pub 2).val).val) pub
      (Schedule.LevelCalendar.header A pub m) m := by
  refine ⟨?_,strideEq⟩
  unfold Schedule.LevelCalendar.header
  rw [dir, pitch, total, ← dir, strideEq, dir]
  simp only [levelStart, levelsBase, Nat.cast_add, Nat.cast_mul]
  ring

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}

/-- The first five persistent scalars describe the actual selected step, including
its residual lanes and next degree. The sixth scalar is the fixed expander degree
for a refresh. -/
structure Published (L : DescriptorSpace.Layout) (i : ℕ) (v : SelectedLevel B f hf) (dH : ℕ)
    (m : Memory w) : Prop where
  room : (levelStart L) i + 5 < 2^w
  vertices : m ((levelStart L) i+0) = (Fintype.card v.input.Base : Word w)
  degree : m ((levelStart L) i+1) = ((2^v.inputExponent : ℕ) : Word w)
  lanes : m ((levelStart L) i+2) = ((2^v.inputLanes : ℕ) : Word w)
  residual : m ((levelStart L) i+3) = ((2^v.outputLanes : ℕ) : Word w)
  nextDegree : m ((levelStart L) i+4) = ((2^v.outputExponent : ℕ) : Word w)
  expander : m ((levelStart L) i+5) = (dH : Word w)

theorem eval_dimensions {step dH : ℕ} {v : SelectedLevel B f hf} (e : Entry L first pub state m)
    (h : Published L (first + step) v dH m) :
    (sites step).eval pub state m = (v.input.positions : Word w) ∧
      (slots step).eval pub state m = (v.oldSlots : Word w) ∧
      (residualLanes step).eval pub state m = ((2^v.outputLanes : ℕ) : Word w) ∧
      (nextDegree step).eval pub state m = ((2^v.outputExponent : ℕ) : Word w) ∧
      (expanderDegree step).eval pub state m = (dH : Word w) := by
  have room := h.room
  have hv := (eval_scalar e step 0 (by omega)).trans h.vertices
  have hd := (eval_scalar e step 1 (by omega)).trans h.degree
  have hl := (eval_scalar e step 2 (by omega)).trans h.lanes
  have hs : (sites step).eval pub state m = (v.input.positions : Word w) := by
    change (scalar step 0).eval pub state m * (scalar step 2).eval pub state m = _
    have hc := (Fintype.card_congr (bitWordFinEquiv v.inputLanes)).trans (Fintype.card_fin _)
    rw [hv,hl,State.positions,Fintype.card_prod,hc,Nat.cast_mul]
  refine ⟨hs,?_, (eval_scalar e step 3 (by omega)).trans h.residual,
    (eval_scalar e step 4 (by omega)).trans h.nextDegree,
    (eval_scalar e step 5 room).trans h.expander⟩
  change (sites step).eval pub state m * (scalar step 1).eval pub state m = _
  rw [hs, hd, SelectedLevel.oldSlots, Nat.cast_mul]

/-- Pack the actual chronological directory before the headers. Capacities of
all persistent per-level arrays and the relative field offsets are preserved. -/
def tightDirectory (L : DescriptorSpace.Layout) (rows : ℕ) : DescriptorSpace.Layout :=
  { L with shape := { L.shape with initialRows := rows, levelPasses := 0, sitePasses := 0 } }

theorem tight_rows (L : DescriptorSpace.Layout) (rows : ℕ) : (directoryRows
    (tightDirectory L rows)) = rows := by
  simp [tightDirectory, directoryRows, passesPerLevel]

theorem tight_stride (L : DescriptorSpace.Layout) (rows : ℕ) : (levelWords
    (tightDirectory L rows)) = (levelWords L) := rfl

theorem tight_end (L : DescriptorSpace.Layout) (rows : ℕ) (h : rows ≤ (directoryRows L)) :
    (endAddress (tightDirectory L rows)) ≤ (endAddress L) := by
  change (directoryBase L) + (directoryRows (tightDirectory L rows))*(L.shape.arity+3)
    + L.levels*(levelWords L) ≤
    (directoryBase L) + (directoryRows L)*(L.shape.arity+3) + L.levels*(levelWords L)
  rw [tight_rows]
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _) _

theorem calendar_capacity (L : DescriptorSpace.Layout) (initial phases blocks : ℕ)
    (hi : initial ≤ L.shape.initialRows) (hb : blocks ≤ L.levels)
    (hp : phases ≤ (passesPerLevel L)) : initial+blocks*phases ≤ (directoryRows L) :=
  Nat.add_le_add hi (Nat.mul_le_mul hb hp)

end CompressorRecords.LevelFields

end VPVNP
end Computability
end OAI
