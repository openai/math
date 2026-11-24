import OAI.Computability.VPVNP.CompressorRecordsBlockPlanner
import OAI.Computability.VPVNP.CompressorRecordsShrinkGreedyLayout
import OAI.Computability.VPVNP.CompressorGreedyRelocated
import OAI.Computability.VPVNP.CompressorRecordsShrinkTagColumn

/-!
# Planning the ordered greedy scans for a shrinking level

The initializer receives the current level's base mate pointers in its public
frame. The color and tag labels occupy separate arenas, each immediately
followed by its fixed-stride records. A read starts at the first record and
stops at the address just past the last record.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.GreedyLevelPlan

open BurstRAM BurstRAM.PrivateRAM Compression PhaseRecipe BlockPlanner Greedy
open scoped Fin.CommRing

private def firstRecord (step : ℕ) (labels : Expr) := labels.add (LevelFields.vertices step)
private def recordsEnd (step width : ℕ) (labels : Expr) :=
  (firstRecord step labels).add ((LevelFields.vertices step).mul (.lit (2 + width)))

/-- Starting address of the tag-label arena, immediately following the color labels and
records. -/
def offsetBase (step a : ℕ) (origin : Expr) := recordsEnd step (2 * 2 ^ a) origin
/-- Starting address of the extracted shifts, immediately following the tag labels and records. -/
def shiftBase (step a : ℕ) (origin : Expr) :=
  recordsEnd step (4 * WalkLayout.tagCount (2 ^ a)) (offsetBase step a origin)
/-- Address of the shared zero word following all per-port shifts. -/
def zeroAddress (step a : ℕ) (origin : Expr) :=
  (shiftBase step a origin).add ((LevelFields.vertices step).mul (LevelFields.degree step))
/-- Exclusive end of the greedy scratch region, one word past the shared zero cell. -/
def greedyStop (step a : ℕ) (origin : Expr) := (zeroAddress step a origin).add (.lit 1)

private def controls (shape : DescriptorSpace.Shape) (step width : ℕ)
    (displacements labels zero : Expr) : Fin 8 → Expr :=
  ![LevelFields.degree step, LevelFields.incidence shape step 0, LevelFields.incidence shape step 1,
    displacements, labels, zero, firstRecord step labels, .lit (2 + width)]

private def prepare {d : ℕ} (shape : DescriptorSpace.Shape) (step width : ℕ)
    (rows : OperandRows d) (displacements labels zero : Expr) : Visit :=
  ⟨Relocated.preparePass rows, .lit 0, LevelFields.vertices step,
    Fin.addCases (fun i ↦ .lit i.val) (controls shape step width displacements labels zero)⟩

private def read (step arity tests width : ℕ) (labels : Expr) : Visit :=
  ops (visitCode arity tests) 4 (firstRecord step labels) (recordsEnd step width labels) Fin.elim0

/-- Calendar visit that prepares the color-test operand records for every base vertex. -/
def colorPrepare (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr) : Visit :=
  prepare shape step (2 * 2 ^ a) (colorOperandRows (2 ^ a)) (LevelFields.incidence shape step 2)
    origin (zeroAddress step a origin)

/-- Calendar visit that scans the prepared color records to assign the greedy color labels. -/
def colorRead (step a : ℕ) (origin : Expr) : Visit := read step 1 (2 * 2 ^ a) (2 * 2 ^ a) origin

/-- Calendar visit that prepares the four-operand tag tests from the extracted shifts and label
tables. -/
def tagPrepare (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr) : Visit :=
  prepare shape step (4 * WalkLayout.tagCount (2 ^ a)) (tagOperandRows (2 ^ a))
    (shiftBase step a origin) (offsetBase step a origin) (zeroAddress step a origin)

/-- Calendar visit that scans the prepared tag records to assign the greedy tag labels. -/
def tagRead (step a : ℕ) (origin : Expr) : Visit :=
  read step 4 (WalkLayout.tagCount (2 ^ a)) (4 * WalkLayout.tagCount (2 ^ a)) (offsetBase step a origin)

/-- The four greedy walk visits in order, preparing and scanning colors before preparing and
scanning tags. -/
def walkVisits (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr) : List Visit :=
  [colorPrepare shape step a origin, colorRead step a origin,
   tagPrepare shape step a origin, tagRead step a origin]

private def projectionParams (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr) : Fin 5 → Expr :=
  ![LevelFields.incidence shape step 2, shiftBase step a origin, zeroAddress step a origin,
    LevelFields.residualLanes step, .lit (2 ^ Shrink.J a)]

/-- Calendar visit that projects the old incidence shifts into the scratch shift column, one
row per base port. -/
def extractShifts (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr) : Visit :=
  ⟨ShrinkTagColumn.extractPass, .lit 0, (LevelFields.vertices step).mul (LevelFields.degree step),
    projectionParams shape step a origin⟩

/-- Single-row visit that initializes the shared zero cell used by the greedy walks. -/
def publishZero (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr) : Visit :=
  ⟨ShrinkTagColumn.zeroPass, .lit 0, .lit 1, projectionParams shape step a origin⟩

/-- Project the displacement and install the zero operand before preparing either directory. -/
def visits (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr) : List Visit :=
  extractShifts shape step a origin :: publishZero shape step a origin :: walkVisits shape step a origin

@[simp] theorem visits_length (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr) :
    (visits shape step a origin).length = 6 := rfl

theorem operand_counts (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr) :
    (visits shape step a origin).map (fun v ↦ v.worker.params) =
      [5, 5, (2 ^ a + 1) + 8, 0, (2 ^ a + 1) + 8, 0] := rfl

variable {w : ℕ} {pub : Fin 5 → Word w} {state : Word w} {m : Memory w}
variable {shape : DescriptorSpace.Shape} {step a n g start : ℕ} {origin : Expr} {T : IncidenceDirectory w}

/-- Values supplied by the physical level header and the chosen scratch origin. -/
structure Reads (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr)
    (pub : Fin 5 → Word w) (state : Word w) (m : Memory w) (n g start : ℕ) (T : IncidenceDirectory w) : Prop where
  vertices : (LevelFields.vertices step).eval pub state m = (n : Word w)
  degree : (LevelFields.degree step).eval pub state m = ((2 ^ a : ℕ) : Word w)
  residual : (LevelFields.residualLanes step).eval pub state m = ((2 ^ g : ℕ) : Word w)
  incidence : ∀ c, (LevelFields.incidence shape step c).eval pub state m = T.column c
  origin : origin.eval pub state m = (start : Word w)

theorem Reads.of_published {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
    {B : S.Templates} {f : B.Entry → R} {hf : B.IsSolution f} (v : SelectedLevel B f hf)
    {layout : DescriptorSpace.Layout} {first expander : ℕ} (e : LevelFields.Entry layout first pub state m)
    (h : LevelFields.Published layout (first + step) v expander m)
    (heads : ∀ c, (DescriptorSpace.incidenceHead layout (first + step) c) < 2 ^ w ∧
      m (DescriptorSpace.incidenceHead layout (first + step) c) = T.column c)
    (address : origin.eval pub state m = (start : Word w)) :
    Reads layout.shape step v.inputExponent origin pub state m (Fintype.card v.input.Base) v.outputLanes start T := by
  have room := h.room
  exact ⟨(LevelFields.eval_scalar e step 0 (by omega)).trans h.vertices,
    (LevelFields.eval_scalar e step 1 (by omega)).trans h.degree,
    (LevelFields.eval_scalar e step 3 (by omega)).trans h.residual,
    fun c ↦ (LevelFields.eval_incidence e step c (heads c).1).trans (heads c).2, address⟩

variable (h : Reads shape step a origin pub state m n g start T)

include h

private theorem eval_firstRecord (labels : Expr) (z : ℕ) (hl : labels.eval pub state m = (z : Word w)) :
    (firstRecord step labels).eval pub state m = ((z + n : ℕ) : Word w) := by
  change labels.eval pub state m + (LevelFields.vertices step).eval pub state m = _
  rw [hl, h.vertices, Nat.cast_add]

private theorem eval_recordsEnd (labels : Expr) (width z : ℕ) (hl : labels.eval pub state m = (z : Word w)) :
    (recordsEnd step width labels).eval pub state m = ((z + n + n * (2 + width) : ℕ) : Word w) := by
  change (firstRecord step labels).eval pub state m + (LevelFields.vertices step).eval pub state m *
    ((2 + width : ℕ) : Word w) = _
  simp only [eval_firstRecord h _ _ hl, h.vertices, Nat.cast_add, Nat.cast_mul]

theorem eval_offsetBase : (offsetBase step a origin).eval pub state m = (GreedyArena.offsetBase start n a : Word w) :=
  eval_recordsEnd h _ _ _ h.origin

theorem eval_shiftBase : (shiftBase step a origin).eval pub state m = (GreedyArena.shiftBase start n a : Word w) :=
  eval_recordsEnd h _ _ _ (eval_offsetBase h)

theorem eval_zeroAddress : (zeroAddress step a origin).eval pub state m = (GreedyArena.zeroCell start n a : Word w) := by
  change (shiftBase step a origin).eval pub state m +
    (LevelFields.vertices step).eval pub state m * (LevelFields.degree step).eval pub state m = _
  rw [eval_shiftBase h, h.vertices, h.degree, GreedyArena.zeroCell, Nat.cast_add, Nat.cast_mul]

theorem eval_greedyStop : (greedyStop step a origin).eval pub state m = (GreedyArena.greedyStop start n a : Word w) := by
  change (zeroAddress step a origin).eval pub state m + (1 : ℕ) = _
  rw [eval_zeroAddress h, GreedyArena.greedyStop, Nat.cast_add]

private theorem prepare_values {width : ℕ} (rows : OperandRows (2 ^ a)) (disps labels zero : Expr)
    (L : WalkLayout w n width) (hl : labels.eval pub state m = (L.origin : Word w)) :
    let v := prepare shape step width rows disps labels zero
    let bank := GreedyArena.tables T a (L.origin : Word w) (zero.eval pub state m) (disps.eval pub state m)
    v.initial.eval pub state m = 0 ∧ v.stop.eval pub state m = (n : Word w) ∧
      (fun j ↦ (v.params j).eval pub state m) = Relocated.publicWords (2 ^ a) L bank := by
  refine ⟨rfl, h.vertices, funext fun j ↦ ?_⟩
  cases j using Fin.addCases with
  | left i => simp [prepare, Relocated.publicWords, slotNumbers, Expr.eval]
  | right i =>
    simp only [prepare, Relocated.publicWords, Fin.addCases_right]
    fin_cases i
    · exact h.degree
    · exact h.incidence 0
    · exact h.incidence 1
    · rfl
    · exact hl
    · rfl
    · change (firstRecord step labels).eval pub state m = L.base 0
      rw [eval_firstRecord h _ _ hl, WalkLayout.base, Nat.zero_mul, Nat.add_zero]
      rfl
    · rfl

private theorem read_values {width : ℕ} (arity tests : ℕ) (labels : Expr)
    (L : WalkLayout w n width) (hl : labels.eval pub state m = (L.origin : Word w)) :
    let v := read step arity tests width labels
    v.initial.eval pub state m = L.base 0 ∧ v.stop.eval pub state m = L.base n ∧
      (fun j ↦ (v.params j).eval pub state m) = Fin.elim0 := by
  exact ⟨by
    change (firstRecord step labels).eval pub state m = L.base 0
    rw [eval_firstRecord h _ _ hl, WalkLayout.base, Nat.zero_mul, Nat.add_zero]
    rfl,
    eval_recordsEnd h _ _ _ hl, funext fun j ↦ Fin.elim0 j⟩

private theorem projection_values :
    (fun j ↦ (projectionParams shape step a origin j).eval pub state m) =
      ShrinkTagColumn.params T a g (GreedyArena.shiftBase start n a : Word w) (GreedyArena.zeroCell start n a : Word w) := by
  funext j
  fin_cases j
  · exact h.incidence 2
  · exact eval_shiftBase h
  · exact eval_zeroAddress h
  · exact h.residual
  · rfl

theorem extractShifts_values :
    let v := extractShifts shape step a origin
    v.initial.eval pub state m = 0 ∧ v.stop.eval pub state m = ((n * 2 ^ a : ℕ) : Word w) ∧
      (fun j ↦ (v.params j).eval pub state m) =
        ShrinkTagColumn.params T a g (GreedyArena.shiftBase start n a : Word w) (GreedyArena.zeroCell start n a : Word w) := by
  refine ⟨rfl, ?_, projection_values h⟩
  change (LevelFields.vertices step).eval pub state m * (LevelFields.degree step).eval pub state m = _
  rw [h.vertices, h.degree, Nat.cast_mul]

theorem publishZero_values :
    let v := publishZero shape step a origin
    v.initial.eval pub state m = 0 ∧ v.stop.eval pub state m = 1 ∧
      (fun j ↦ (v.params j).eval pub state m) =
        ShrinkTagColumn.params T a g (GreedyArena.shiftBase start n a : Word w) (GreedyArena.zeroCell start n a : Word w) :=
  ⟨rfl, rfl, projection_values h⟩

variable (room : GreedyArena.greedyStop start n a < 2 ^ w)

theorem colorPrepare_values :
    let L := GreedyArena.colorLayout w start n a room
    let bank := GreedyArena.tables T a (start : Word w) (GreedyArena.zeroCell start n a : Word w) T.shift
    let v := colorPrepare shape step a origin
    v.initial.eval pub state m = 0 ∧ v.stop.eval pub state m = (n : Word w) ∧
      (fun j ↦ (v.params j).eval pub state m) = Relocated.publicWords (2 ^ a) L bank := by
  have shift : (LevelFields.incidence shape step 2).eval pub state m = T.shift := h.incidence 2
  simpa only [colorPrepare, GreedyArena.colorLayout, GreedyArena.colorBase, eval_zeroAddress h, shift] using prepare_values h (colorOperandRows (2 ^ a))
    (LevelFields.incidence shape step 2) origin (zeroAddress step a origin) (GreedyArena.colorLayout w start n a room) h.origin

theorem colorRead_values :
    let L := GreedyArena.colorLayout w start n a room
    let v := colorRead step a origin
    v.initial.eval pub state m = L.base 0 ∧ v.stop.eval pub state m = L.base n ∧
      (fun j ↦ (v.params j).eval pub state m) = Fin.elim0 :=
  read_values h _ _ origin _ h.origin

theorem tagPrepare_values :
    let L := GreedyArena.tagLayout w start n a room
    let bank := GreedyArena.tables T a (GreedyArena.offsetBase start n a : Word w)
      (GreedyArena.zeroCell start n a : Word w) (GreedyArena.shiftBase start n a : Word w)
    let v := tagPrepare shape step a origin
    v.initial.eval pub state m = 0 ∧ v.stop.eval pub state m = (n : Word w) ∧
      (fun j ↦ (v.params j).eval pub state m) = Relocated.publicWords (2 ^ a) L bank := by
  simpa only [tagPrepare, GreedyArena.tagLayout, eval_zeroAddress h, eval_shiftBase h] using prepare_values h (tagOperandRows (2 ^ a))
    (shiftBase step a origin) (offsetBase step a origin) (zeroAddress step a origin)
    (GreedyArena.tagLayout w start n a room) (eval_offsetBase h)

theorem tagRead_values :
    let L := GreedyArena.tagLayout w start n a room
    let v := tagRead step a origin
    v.initial.eval pub state m = L.base 0 ∧ v.stop.eval pub state m = L.base n ∧
      (fun j ↦ (v.params j).eval pub state m) = Fin.elim0 :=
  read_values h _ _ (offsetBase step a origin) _ (eval_offsetBase h)

end CompressorRecords.GreedyLevelPlan

end VPVNP
end Computability
end OAI
