import OAI.Computability.VPVNP.CompressorRecordsDirectory
import OAI.Computability.VPVNP.CompressorRecordsWorkspace
import OAI.Computability.VPVNP.CompressorRecordIncidenceLayout

/-!
# Descriptor addresses across compressor levels

Appendix E uses a fixed number of words per slot and position. We allocate
the controller header, its active frame and its directory first. Each level
then has a persistent header, six packed incidence columns, and rectangular
tables of fixed-width slot records. The old levels remain addressable
after the next level has been written. The initial column addresses agree
with the native cursor scan. Both exclusive cursors and addresses fit a
machine word throughout the logarithmic block schedule.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DescriptorSpace

open BurstRAM CursorBounds Filter
open scoped Fin.CommRing

/-- Fixed record dimensions of the program. A directory can contain both
whole-level passes and site-specific rows. The native workspace reserves
the runtime level stride immediately after the active frame. -/
structure Shape where
  /-- Number of parameter words in the planner's active frame and in each directory row. -/
  arity : ℕ
  /-- Number of directory rows reserved for initialization before any per-level visits. -/
  initialRows : ℕ
  /-- Number of whole-level passes scheduled at each level, independently of the number of
  positions. -/
  levelPasses : ℕ
  /-- Number of site-specific directory rows reserved per position at each level. -/
  sitePasses : ℕ
  /-- Number of scalar words preceding the incidence and table pointers in a level header. -/
  scalarFields : ℕ
  /-- Number of rectangular slot-record tables reserved at each level. -/
  tables : ℕ
  /-- Maximum number of slots reserved per position in a level's incidence columns and tables. -/
  slots : ℕ
  /-- Number of words in a single slot record of a rectangular table. -/
  fields : ℕ

/-- All levels use the initial position count as their rectangular capacity. -/
structure Layout where
  /-- Fixed dimensions of the directory, level headers, incidence columns, and slot records. -/
  shape : Shape
  /-- Starting address of the controller workspace that precedes the active frame and
  directory. -/
  base : ℕ
  /-- Initial position count used as the common rectangular capacity across levels. -/
  positions : ℕ
  /-- Number of persistent level regions allocated after the directory. -/
  levels : ℕ

variable (L : Layout)

/-- Starting address of the active frame, nine words past the controller workspace base. -/
def frameBase := L.base + 9
/-- Address reserved immediately after the active frame and immediately before the directory. -/
def plannerTag := frameBase L + (L.shape.arity + 1)
/-- Starting address of the first scheduler directory row, just past the planner tag cell. -/
def directoryBase := plannerTag L + 1
/-- Number of directory rows per level, combining whole-level passes and site passes for every
position. -/
def passesPerLevel := L.shape.levelPasses + L.shape.sitePasses * L.positions
/-- Total directory row count for initialization and all allocated levels. -/
def directoryRows := L.shape.initialRows + L.levels * passesPerLevel L
/-- Address of the first level header, after all fixed-width directory rows. -/
def levelsBase := directoryBase L + directoryRows L * (L.shape.arity + 3)
/-- Size in words of the scalar header, six incidence pointers, and one pointer per table. -/
def levelHeaderWords := L.shape.scalarFields + 6 + L.shape.tables
/-- Number of slots available in a full level, obtained by multiplying positions by slots per
position. -/
def slotCapacity := L.positions * L.shape.slots
/-- Size in words of one rectangular table containing a fixed-width record for every reserved
slot. -/
def tableWords := slotCapacity L * L.shape.fields
/-- Word stride between successive levels, including the header, all incidence columns, and all
tables. -/
def levelWords := levelHeaderWords L + 6 * slotCapacity L + L.shape.tables * tableWords L
/-- Address of the header at the given zero-based level index. -/
def levelStart (level : ℕ) := levelsBase L + level * levelWords L
/-- First address beyond the final allocated level. -/
def endAddress := levelStart L L.levels

/-- Persistent level scalars, including vertex count, degree, row count,
residual lane count and the operands of the next refresh. -/
def scalarHead (level : ℕ) (j : Fin L.shape.scalarFields) := levelStart L level + j.val

/-- Pointers to the six incidence columns in the native directory order. -/
def incidenceHead (level : ℕ) (c : Fin 6) := levelStart L level + L.shape.scalarFields + c.val

/-- Pointers to the record tables of the particular compressor pass. -/
def tableHead (level : ℕ) (a : Fin L.shape.tables) :=
  levelStart L level + L.shape.scalarFields + 6 + a.val

/-- Address of the first incidence column immediately after this level's header. -/
def incidenceStart (level : ℕ) := levelStart L level + levelHeaderWords L

/-- Native scans pack the incidence columns with their actual row count. The
unused part of the reserved region stays available as blank space. -/
def incidenceBase (level rows : ℕ) (c : Fin 6) := incidenceStart L level + c.val * rows

/-- Starting address of the rectangular tables after the six incidence columns of this level. -/
def arrayBase (level : ℕ) := incidenceStart L level + 6 * slotCapacity L

/-- Starting address of the specified rectangular table within the level. -/
def tableBase (level : ℕ) (a : Fin L.shape.tables) := arrayBase L level + a.val * tableWords L

/-- Coordinates of a table word, indexed by table, position, slot, and record field. -/
abbrev Cell := Fin L.shape.tables × Fin L.positions × Fin L.shape.slots × Fin L.shape.fields

/-- Site-major, slot-major, field-minor addressing within each array. -/
def cellAddress (level : ℕ) (k : Cell L) :=
  tableBase L level k.1 + (k.2.1.val * L.shape.slots + k.2.2.1.val) * L.shape.fields + k.2.2.2.val

/-- Disjoint scalar, incidence-head and array-head fields, with a finite
equivalence giving their word offsets from the start of the level. -/
def headerIndex : ((Fin L.shape.scalarFields ⊕ Fin 6) ⊕ Fin L.shape.tables) ≃
    Fin (levelHeaderWords L) :=
  ((finSumFinEquiv (m := L.shape.scalarFields) (n := 6)).sumCongr (Equiv.refl _)).trans finSumFinEquiv

theorem scalarHead_index (level : ℕ) (j : Fin L.shape.scalarFields) :
    scalarHead L level j = levelStart L level + (headerIndex L (.inl (.inl j))).val := rfl

theorem incidenceHead_index (level : ℕ) (c : Fin 6) :
    incidenceHead L level c = levelStart L level + (headerIndex L (.inl (.inr c))).val := by
  change _ = _ + (L.shape.scalarFields + c.val)
  simp [incidenceHead, Nat.add_assoc]

theorem tableHead_index (level : ℕ) (a : Fin L.shape.tables) :
    tableHead L level a = levelStart L level + (headerIndex L (.inr a)).val := by
  change _ = _ + (L.shape.scalarFields + 6 + a.val)
  simp [tableHead, Nat.add_assoc]

theorem directoryAddress_lt (i : Fin (directoryRows L)) (j : Fin (L.shape.arity + 3)) :
    Schedule.Directory.address (directoryBase L) L.shape.arity i.val j < levelsBase L := by
  have h := Nat.mul_le_mul_right (L.shape.arity + 3) i.isLt
  rw [Nat.succ_mul] at h
  have hj := j.isLt
  unfold Schedule.Directory.address levelsBase
  omega

theorem levelOrdinal_lt (level : Fin L.levels) (pass : Fin (passesPerLevel L)) :
    Schedule.Directory.levelOrdinal L.shape.initialRows level.val pass < directoryRows L := by
  have h := Nat.mul_le_mul_right (passesPerLevel L) level.isLt
  rw [Nat.succ_mul] at h
  have hp := pass.isLt
  unfold Schedule.Directory.levelOrdinal directoryRows
  omega

private def cellIndex : Cell L ≃ Fin (L.shape.tables * (L.positions * (L.shape.slots * L.shape.fields))) :=
  ((Equiv.refl _).prodCongr (((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv)).trans
    finProdFinEquiv

private theorem cell_eq (level : ℕ) (k : Cell L) :
    cellAddress L level k = arrayBase L level + (cellIndex L k).val := by
  change arrayBase L level + k.1.val * tableWords L +
    (k.2.1.val * L.shape.slots + k.2.2.1.val) * L.shape.fields + k.2.2.2.val =
    arrayBase L level + (k.2.2.2.val + L.shape.fields * k.2.2.1.val +
      (L.shape.slots * L.shape.fields) * k.2.1.val +
      (L.positions * (L.shape.slots * L.shape.fields)) * k.1.val)
  simp only [tableWords, slotCapacity]
  ring

theorem cellAddress_injective (level : ℕ) : Function.Injective (cellAddress L level) := by
  intro k k' hk
  rw [cell_eq, cell_eq] at hk
  exact (cellIndex L).injective (Fin.ext (Nat.add_left_cancel hk))

theorem cellAddress_bounds (level : ℕ) (k : Cell L) :
    arrayBase L level ≤ cellAddress L level k ∧ cellAddress L level k < levelStart L (level + 1) := by
  rw [cell_eq]
  refine ⟨Nat.le_add_right .., ?_⟩
  have hi : (cellIndex L k).val < L.shape.tables * tableWords L := by
    simpa only [tableWords, slotCapacity, Nat.mul_assoc] using (cellIndex L k).isLt
  simp only [arrayBase, incidenceStart, levelStart, Nat.succ_mul, levelWords] at *
  omega

/-- Consecutive table IDs give nonoverlapping physical intervals. -/
theorem tableEnd_le_tableBase (level : ℕ) {a b : Fin L.shape.tables} (h : a < b) :
    tableBase L level a + tableWords L ≤ tableBase L level b := by
  have hmul := Nat.mul_le_mul_right (tableWords L) (Nat.succ_le_of_lt h)
  rw [Nat.succ_mul] at hmul
  simp only [tableBase]
  omega

theorem tableEnd_le_nextLevel (level : ℕ) (a : Fin L.shape.tables) :
    tableBase L level a + tableWords L ≤ levelStart L (level+1) := by
  have hmul := Nat.mul_le_mul_right (tableWords L) a.isLt
  rw [Nat.succ_mul] at hmul
  simp only [tableBase, arrayBase, incidenceStart, levelStart, Nat.succ_mul, levelWords]
  omega

theorem incidence_bounds (level rows : ℕ) (hr : rows ≤ slotCapacity L) (c : Fin 6) (i : Fin rows) :
    incidenceStart L level ≤ incidenceBase L level rows c + i.val ∧
      incidenceBase L level rows c + i.val < arrayBase L level := by
  have hc := Nat.mul_le_mul_right rows c.isLt
  have hcap := Nat.mul_le_mul_left 6 hr
  rw [Nat.succ_mul] at hc
  have hi := i.isLt
  simp only [incidenceBase, arrayBase]
  omega

theorem levelStart_mono : Monotone (levelStart L) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

/-- A store in a later level cannot overwrite a word in an earlier level.
The statement applies to an entire chronological native event trace. -/
theorem olderLevel_preserved {w : ℕ} (m : Memory w) (es : List (Event w)) {i j addr : ℕ}
    (hij : i < j) (hbase : levelsBase L ≤ addr) (ha : addr < levelStart L (i + 1))
    (writes : ∀ a v, Event.write a v ∈ es → a.val < levelsBase L ∨ levelStart L j ≤ a.val) :
    after m es addr = m addr := by
  have hlt := ha.trans_le (levelStart_mono L hij)
  induction es generalizing m with
  | nil => rfl
  | cons e es ih =>
    change after (update m e) es addr = _
    rw [ih _ (fun a v he ↦ writes a v (List.mem_cons_of_mem _ he))]
    cases e with
    | write a v =>
      have hne : addr ≠ a.val := (writes a v (List.mem_cons_self ..)).elim
        (fun hw ↦ (hw.trans_le hbase).ne') (fun hw ↦ (hlt.trans_le hw).ne)
      simp [update, writeMemory, hne]
    | _ => rfl

/-- The exclusive upper end and every intermediate level start fit under
one common bound. -/
theorem level_room {w : ℕ} (fit : endAddress L < 2^w) (i : Fin L.levels) :
    levelStart L (i.val + 1) < 2^w :=
  (levelStart_mono L i.isLt).trans_lt fit

private theorem incidence_end_le (level : ℕ) :
    arrayBase L level ≤ levelStart L (level + 1) := by
  simp only [arrayBase, incidenceStart, levelStart, Nat.succ_mul, levelWords]
  omega

theorem packed_incidence_room {w : ℕ} (fit : endAddress L < 2^w) (i : Fin L.levels)
    {rows : ℕ} (hr : rows ≤ slotCapacity L) :
    incidenceStart L i + 6 * rows < 2^w := by
  apply lt_of_le_of_lt _ (level_room L fit i)
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hr) _).trans (incidence_end_le L i)

/-- Packed column heads as used by the typed incidence directory. -/
def packedIncidence (w level rows : ℕ) : IncidenceDirectory w :=
  let col (c : Fin 6) := CursorRAM.encode w (incidenceBase L level rows c)
  ⟨col 0, col 1, col 2, col 3, col 4, col 5⟩

theorem packed_column (w level rows : ℕ) (c : Fin 6) :
    (packedIncidence L w level rows).column c = CursorRAM.encode w (incidenceBase L level rows c) := by
  fin_cases c <;> rfl

theorem packed_layout {w a l : ℕ} (X : Compression.State a l) (level : Fin L.levels)
    (fit : endAddress L < 2^w)
    (hrows : Fintype.card X.Base * 2^l * 2^a ≤ slotCapacity L) :
    (packedIncidence L w level (Fintype.card X.Base * 2^l * 2^a)).Layout X := by
  let rows := Fintype.card X.Base * 2^l * 2^a
  have room := packed_incidence_room L fit level hrows
  apply IncidenceDirectory.Layout.packed X (incidenceStart L level) room.le
  intro c
  rw [packed_column]
  have hc := Nat.mul_le_mul_right rows c.isLt.le
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.add_le_add_left hc _) room)

/-- The native scheduler's published frame, directory and control addresses. -/
def ports (w : ℕ) : Schedule.Ports w :=
  Workspace.ports L.shape.arity (CursorRAM.encode w L.base)

theorem frame_before_directory : frameBase L + (L.shape.arity + 1) ≤ directoryBase L :=
  Nat.le_add_right ..

theorem directoryBase_le_end : directoryBase L ≤ endAddress L :=
  (Nat.le_add_right .. : directoryBase L ≤ levelsBase L).trans (Nat.le_add_right ..)

private theorem word_add_val {w : ℕ} (base : Word w) {j : ℕ} (fit : base.val + j < 2^w) :
    (base + (j : Word w)).val = base.val + j := by
  rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : j < 2^w), Nat.mod_eq_of_lt fit]

theorem ports_values {w : ℕ} (fit : endAddress L < 2^w) :
    (ports L w).activeFrame.val = frameBase L ∧ (ports L w).directory.val = directoryBase L ∧
      (ports L w).ordinal.val = L.base + 7 ∧ (ports L w).rows.val = L.base + 8 ∧
      (ports L w).tag.val = L.base + 6 := by
  have hdir := (directoryBase_le_end L).trans_lt fit
  have hframe := (frame_before_directory L).trans_lt hdir
  dsimp only [frameBase] at hframe
  have hb : (CursorRAM.encode w L.base).val = L.base := Nat.mod_eq_of_lt (by omega)
  have add (j : ℕ) (hj : j ≤ 9) : (CursorRAM.encode w L.base + (j : Word w)).val = L.base + j := by
    rw [word_add_val, hb]
    omega
  have dir : (ports L w).directory.val = directoryBase L := by
    change (CursorRAM.encode w L.base + ((11 + L.shape.arity : ℕ) : Word w)).val = _
    rw [word_add_val, hb]
    · simp only [directoryBase, plannerTag, frameBase]
      omega
    · rw [hb]
      simp only [directoryBase, plannerTag, frameBase] at hdir
      omega
  exact ⟨add 9 le_rfl, dir, add 7 (by decide), add 8 (by decide), add 6 (by decide)⟩

theorem frameFits {w d : ℕ} (C : Schedule.Catalog d) (hC : Schedule.arity C = L.shape.arity)
    (fit : endAddress L < 2^w) : Schedule.Directory.FrameFits C (ports L w) := by
  have hval := ports_values L fit
  have hfit := ((frame_before_directory L).trans (directoryBase_le_end L)).trans_lt fit
  rw [← hC] at hfit
  constructor
  · omega
  · intro j
    have hj := j.isLt
    have haddr := word_add_val (ports L w).activeFrame (j := j.val) (by rw [hval.1]; omega)
    rw [hval.1] at haddr
    have h₁ := hval.2.2.1
    have h₂ := hval.2.2.2.2
    unfold frameBase at haddr
    constructor <;> intro e <;> have := congrArg Fin.val e <;> omega

theorem cursor_directory_eq (w level b l a : ℕ) :
    packedIncidence L w level (CursorRAM.rowCount b l a) =
      CursorRAM.directory w b l a (incidenceStart L level) := rfl

/-- One workspace prefix, before accounting for the per-level rows. -/
def Shape.fixedWords (F : Shape) := 11 + F.arity + F.initialRows * (F.arity + 3)

/-- Constant words per level, comprising header fields and level-wide pass rows. -/
def Shape.levelFixed (F : Shape) := F.scalarFields + 6 + F.tables + F.levelPasses * (F.arity + 3)

/-- Words per position at each level, including native directory rows,
six incidence columns and all rectangular slot records. -/
def Shape.siteWords (F : Shape) :=
  F.sitePasses * (F.arity + 3) + F.slots * (6 + F.tables * F.fields)

theorem endAddress_eq :
    endAddress L = L.base + L.shape.fixedWords +
      L.levels * (L.shape.levelFixed + L.positions * L.shape.siteWords) := by
  simp only [endAddress, levelStart, levelsBase, directoryBase, plannerTag, frameBase, directoryRows,
    passesPerLevel, levelWords, levelHeaderWords, slotCapacity, tableWords,
    Shape.fixedWords, Shape.levelFixed, Shape.siteWords]
  ring

/-- The allocated words are bounded by a fixed constant times positions
times levels whenever both counts are positive. -/
theorem endAddress_le (hp : 0 < L.positions) (hl : 0 < L.levels) :
    endAddress L ≤ L.base + (L.shape.fixedWords + L.shape.levelFixed + L.shape.siteWords) *
      L.positions * L.levels := by
  rw [endAddress_eq]
  have h₁ := Nat.le_mul_of_pos_right L.shape.fixedWords (Nat.mul_pos hp hl)
  have h₂ := Nat.mul_le_mul_left L.levels (Nat.le_mul_of_pos_right L.shape.levelFixed hp)
  nlinarith only [h₁, h₂]

/-- The initial level and one level per substep in the repeated block schedule. -/
noncomputable def cursorLayout (F : Shape) (b steps : ℕ) (θ : ℝ) (base n : ℕ) : Layout :=
  ⟨F, base, initialPositions b n, 1 + (steps + 1) * Compression.blockCount θ n⟩

private theorem bounded_blockCount {θ : ℝ} (hθ : θ ≤ 1) :
    PolynomiallyBounded (Compression.blockCount θ) := by
  apply PolynomiallyBounded.id.of_eventually_le 1
  intro n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.logb_nonneg (by norm_num : 1 < (2 : ℝ)) hn'
  have h : Compression.blockCount θ n ≤ Nat.clog 2 n := by
    rw [Compression.blockCount, ← Real.natCeil_logb_natCast 2 n]
    exact (Nat.floor_le_floor (mul_le_of_le_one_left hlog hθ)).trans (Nat.floor_le_ceil _)
  exact h.trans (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le)

theorem bounded_cursorEnd (F : Shape) (b steps : ℕ) {θ : ℝ} (hθ : θ ≤ 1)
    {base : ℕ → ℕ} (hb : PolynomiallyBounded base) :
    PolynomiallyBounded (fun n ↦ endAddress (cursorLayout F b steps θ (base n) n)) := by
  simp only [endAddress_eq, cursorLayout]
  exact (hb.add (PolynomiallyBounded.const F.fixedWords)).add
    (((PolynomiallyBounded.const 1).add ((PolynomiallyBounded.const (steps+1)).mul
      (bounded_blockCount hθ))).mul ((PolynomiallyBounded.const F.levelFixed).add
      ((CursorRAM.bounded_positions b).mul (PolynomiallyBounded.const F.siteWords))))

theorem cursor_initial_room (F : Shape) (b steps n start a : ℕ) (θ : ℝ) (hd : 2^a ≤ F.slots)
    {baseBits laneBits : ℕ} (he : baseBits + laneBits = virtualBits b n)
    (fit : endAddress (cursorLayout F b steps θ start n) < 2 ^ wordBits b n) :
    let layout := cursorLayout F b steps θ start n
    incidenceStart layout 0 + 6 * CursorRAM.rowCount baseBits laneBits a < 2 ^ wordBits b n := by
  let layout := cursorLayout F b steps θ start n
  let first : Fin layout.levels := ⟨0, by simp [layout, cursorLayout]⟩
  apply packed_incidence_room layout fit first
  rw [CursorRAM.rowCount_eq_positions he]
  exact Nat.mul_le_mul_left _ hd

/-- At the actual cursor dimensions the descriptor workspace and a polynomial
suffix, including their exclusive end cursors, fit in a word. The same threshold
also certifies the first native scan and its timestamps for every base/lane split. -/
theorem eventually_cursor_room (F : Shape) (b a steps : ℕ) (hb : 1 ≤ b) {θ : ℝ} (hθ : θ ≤ 1)
    {base suffix : ℕ → ℕ} (hbase : PolynomiallyBounded base) (hsuffix : PolynomiallyBounded suffix) :
    ∀ᶠ n : ℕ in atTop, let layout := cursorLayout F b steps θ (base n) n
      endAddress layout + suffix n < 2 ^ wordBits b n ∧
      ∀ baseBits laneBits, baseBits + laneBits = virtualBits b n →
        1 < baseBits + laneBits ∧ initialWidth b n < 2 ^ wordBits b n ∧
        incidenceStart layout 0 + 7 * CursorRAM.rowCount baseBits laneBits a ≤ 2 ^ wordBits b n := by
  let L n := cursorLayout F b steps θ (base n) n
  have he := bounded_cursorEnd F b steps hθ hbase
  have hstart : PolynomiallyBounded (fun n ↦ incidenceStart (L n) 0) := by
    apply he.of_le
    intro n
    have h₁ := Nat.le_add_right (incidenceStart (L n) 0) (6 * slotCapacity (L n))
    have h₂ := incidence_end_le (L n) 0
    exact (h₁.trans h₂).trans (levelStart_mono (L n) (by simp [cursorLayout]))
  filter_upwards [CursorRAM.eventual_word_room b hb (he.add hsuffix),
    CursorRAM.eventually_cursorCapacity b a hb hstart] with n hn hi
  exact ⟨hn, fun b' l heq ↦ ⟨(hi b' l heq).1, (hi b' l heq).2.2⟩⟩

end CompressorRecords.DescriptorSpace

end VPVNP
end Computability
end OAI
