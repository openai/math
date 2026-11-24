import OAI.Computability.VPVNP.CompressorRecordsShrinkGreedyPhases
import OAI.Computability.VPVNP.CompressorRecordsShrinkTagColumn

/-!
# Computing the shrinking placement directory from the old incidence table

The tag extraction visits the old outgoing slots and initializes the zero
operand. A color scan and an offset scan then fill their disjoint fresh
directories. The full old displacement word remains available to the
placement worker, while the offset worker sees only the projected tag.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.GreedyArena

open BurstRAM Compression Greedy
open scoped Fin.CommRing

variable {w a g : ℕ}

/-- A compressor state whose lane width supplies the packing fields required by shrinking at
the given degree and residual width. -/
abbrev ShrinkingState (a g : ℕ) := State a (packingLaneBits a g)

/-- Extract the packing-tag component of an outgoing base port's lane displacement for the
offset assignment. -/
def projectedTag (X : ShrinkingState a g) (e : X.Base × Fin (2 ^ a)) : BitWord (Shrink.J a) :=
  (packingFields a g (X.slots.displacement e)).2.2.1

/-- The tag-projection worker's public operands, including the old incidence data and
destinations for projected tags and zero. -/
def projectionWords (T : IncidenceDirectory w) (origin n a g : ℕ) : Fin 5 → Word w :=
  ShrinkTagColumn.params T a g (CursorRAM.encode w (shiftBase origin n a)) (CursorRAM.encode w (zeroCell origin n a))

/-- The memory after scanning all old base ports to write projected displacement tags and
initialize the shared zero operand. -/
def projectedMemory (X : ShrinkingState a g) (T : IncidenceDirectory w) (origin : ℕ) (m : Memory w) : Memory w :=
  let n := Fintype.card X.Base
  after m (eventLog (ShrinkTagColumn.reports (projectionWords T origin n a g) (n * 2 ^ a) m))

/-- The greedy color pass's port tables, using the fresh color column, shared zero, and
original displacements. -/
def colorTables (T : IncidenceDirectory w) (origin n a : ℕ) : PortTables w :=
  tables T a (CursorRAM.encode w (colorBase origin)) (CursorRAM.encode w (zeroCell origin n a)) T.shift

/-- The offset pass's port tables, using the fresh offset column and projected tag
displacements. -/
def tagTables (T : IncidenceDirectory w) (origin n a : ℕ) : PortTables w :=
  tables T a (CursorRAM.encode w (offsetBase origin n a)) (CursorRAM.encode w (zeroCell origin n a))
    (CursorRAM.encode w (shiftBase origin n a))

/-- The report traces of all six native visits, in their memory execution order. -/
structure Run (X : ShrinkingState a g) (T : IncidenceDirectory w) (origin : ℕ) (m : Memory w) where
  room : greedyStop origin (Fintype.card X.Base) a < 2 ^ w
  old : OldBelow X T origin
  input : T.Represents X m
  tagFit : Shrink.J a ≤ w
  projection : ShrinkTagColumn.Result (projectionWords T origin (Fintype.card X.Base) a g)
    (Fintype.card X.Base * 2 ^ a) m
  /-- The executed greedy color assignment in the color walk's workspace. -/
  color : Assignment (colorLayout w origin (Fintype.card X.Base) a room)
    (colorTables T origin (Fintype.card X.Base) a) X.slots.base X.baseIndex (colorOperandRows (2 ^ a))
    1 (2 * 2 ^ a) (projectedMemory X T origin m) (fun v : Fin (Shrink.colors a) => CursorRAM.encode w v.val)
    ((orderedDyadicPacking X.slots X.baseIndex).color)
  /-- The executed tag-offset assignment using the projected displacement table after coloring. -/
  offsets : Assignment (tagLayout w origin (Fintype.card X.Base) a room)
    (tagTables T origin (Fintype.card X.Base) a) X.slots.base X.baseIndex (tagOperandRows (2 ^ a))
    4 (WalkLayout.tagCount (2 ^ a)) color.post (tagWord tagFit) ((orderedDyadicPacking X.slots X.baseIndex).offset)

private theorem destCell (origin n a w i : ℕ) (room : greedyStop origin n a < 2 ^ w) (hi : i < n * 2 ^ a) :
    ShrinkTagColumn.cell (CursorRAM.encode w (shiftBase origin n a)) i = shiftBase origin n a + i := by
  have hstop : shiftBase origin n a + n * 2 ^ a + 1 < 2 ^ w := room
  change ((Fin.ofNat (2 ^ w) (shiftBase origin n a)) + (i : Word w)).val = _
  rw [Fin.val_add, Fin.val_natCast, Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ w),
    Nat.mod_eq_of_lt (by omega : shiftBase origin n a < 2 ^ w), Nat.mod_eq_of_lt (by omega)]

private theorem projection_frame (X : ShrinkingState a g) (T : IncidenceDirectory w) (origin : ℕ) (m : Memory w)
    (room : greedyStop origin (Fintype.card X.Base) a < 2 ^ w)
    (r : ShrinkTagColumn.Result (projectionWords T origin (Fintype.card X.Base) a g) (Fintype.card X.Base * 2 ^ a) m)
    (z : ℕ) (hz : z < shiftBase origin (Fintype.card X.Base) a) :
    projectedMemory X T origin m z = m z := by
  let n := Fintype.card X.Base
  change greedyStop origin n a < 2 ^ w at room
  have hs : zeroCell origin n a < 2 ^ w := Nat.lt_of_succ_lt room
  change z < shiftBase origin n a at hz
  apply r.preserve z
  · change z ≠ (zeroCell origin n a) % (2 ^ w)
    rw [Nat.mod_eq_of_lt hs]; change z ≠ shiftBase origin n a + n * 2 ^ a
    omega
  · intro i hi
    rw [show (projectionWords T origin n a g) 1 = CursorRAM.encode w (shiftBase origin n a) by rfl,
      destCell origin n a w i room hi]
    omega

private theorem shifted_port (X : ShrinkingState a g) (origin : ℕ)
    (room : greedyStop origin (Fintype.card X.Base) a < 2 ^ w) (e : X.Base × Fin (2 ^ a)) :
    (CursorRAM.encode w (shiftBase origin (Fintype.card X.Base) a) + IncidenceDirectory.basePort X e).val =
      shiftBase origin (Fintype.card X.Base) a + (IncidenceDirectory.baseOrder X e).val := by
  rw [IncidenceDirectory.basePort_number]
  exact destCell origin _ a w _ room (IncidenceDirectory.baseOrder X e).isLt

private theorem region (X : ShrinkingState a g) (T : IncidenceDirectory w) (origin : ℕ)
    (old : OldBelow X T origin) (room : greedyStop origin (Fintype.card X.Base) a < 2 ^ w) :
    ShrinkTagColumn.Regions (projectionWords T origin (Fintype.card X.Base) a g) (Fintype.card X.Base * 2 ^ a) := by
  let n := Fintype.card X.Base
  have hb := bounds origin n a
  change origin + n ≤ _ ∧ _ at hb
  have fit := old.baseFits
  change greedyStop origin n a < 2 ^ w at room
  have hs : zeroCell origin n a < 2 ^ w := Nat.lt_of_succ_lt room
  change n * 2 ^ a ≤ origin at fit
  refine ⟨fit.trans (by omega), ?_, ?_⟩
  · intro i j hi hj
    change i < n * 2 ^ a at hi
    change j < n * 2 ^ a at hj
    change (T.shift + (i : Word w)).val ≠ ShrinkTagColumn.cell (CursorRAM.encode w (shiftBase origin n a)) j
    have he : (T.shift + (i : Word w)).val < origin := old.cell 2 _ ((Nat.mod_le i _).trans_lt
      (hi.trans_le (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)))))
    rw [destCell origin n a w j room hj]; omega
  · intro i hi
    change i < n * 2 ^ a at hi
    change ShrinkTagColumn.cell (CursorRAM.encode w (shiftBase origin n a)) i ≠ zeroCell origin n a % (2 ^ w)
    rw [destCell origin n a w i room hi, Nat.mod_eq_of_lt hs]
    change shiftBase origin n a + i ≠ shiftBase origin n a + n * 2 ^ a
    omega

namespace Run

variable {X : ShrinkingState a g} {T : IncidenceDirectory w} {origin : ℕ} {m : Memory w}
variable (r : Run X T origin m)

/-- The final memory of the greedy shrinking run, after the offset assignment completes. -/
def post : Memory w := r.offsets.post

theorem below (z : ℕ) (hz : z < origin) : r.post z = m z := by
  let n := Fintype.card X.Base
  have hb := bounds origin n a
  change origin + n ≤ _ ∧ _ at hb
  exact (r.offsets.frame z (.inl (by change z < offsetBase origin n a; omega))).trans
    ((r.color.frame z (.inl hz)).trans (projection_frame X T origin m r.room r.projection z (by change z < shiftBase origin n a; omega)))

theorem incidence : T.Represents X r.post := r.old.preserve r.input r.below

private theorem address_label {n width : ℕ} (L : WalkLayout w n width) (i : Fin n) :
    CursorRAM.encode w L.origin + CursorRAM.encode w i.val = L.label i := Fin.ext (Nat.add_mod ..).symm

theorem color_at (x : X.Base) :
    r.post (CursorRAM.encode w (colorBase origin) + CursorRAM.encode w (X.baseIndex x).val).val =
      CursorRAM.encode w ((orderedDyadicPacking X.slots X.baseIndex).color x).val := by
  let n := Fintype.card X.Base
  let L := colorLayout w origin n a r.room
  rw [show colorBase origin = L.origin by rfl, address_label]
  apply (r.offsets.frame _ (.inl ?_)).trans (r.color.atLabel x)
  have hx : (X.baseIndex x).val < n := (X.baseIndex x).isLt
  change (L.label (X.baseIndex x)).val < offsetBase origin n a
  rw [WalkLayout.label_val]
  have hb := (bounds origin n a).1
  change colorBase origin + (X.baseIndex x).val < offsetBase origin n a
  omega

theorem offset_at (x : X.Base) :
    r.post (CursorRAM.encode w (offsetBase origin (Fintype.card X.Base) a) + CursorRAM.encode w (X.baseIndex x).val).val =
      tagWord r.tagFit ((orderedDyadicPacking X.slots X.baseIndex).offset x) := by
  let L := tagLayout w origin (Fintype.card X.Base) a r.room
  rw [show offsetBase origin (Fintype.card X.Base) a = L.origin by rfl, address_label]
  exact r.offsets.atLabel x

end Run

/-- Read a natural-number label from an indexed word of a greedy assignment column. -/
def column (m : Memory w) (base : Word w) (i : ℕ) : ℕ := (m (base + CursorRAM.encode w i).val).val

theorem Run.directory {X : ShrinkingState a g} {T : IncidenceDirectory w} {origin : ℕ} {m : Memory w}
    (r : Run X T origin m) : Shrink.Directory X.slots X.baseIndex
      (column r.post (CursorRAM.encode w (colorBase origin)))
      (column r.post (CursorRAM.encode w (offsetBase origin (Fintype.card X.Base) a)))
      (column r.post T.baseOut) (column r.post T.shift) := by
  let n := Fintype.card X.Base
  have hc := colorFits origin n a w Fintype.card_pos r.room
  have hb := bounds origin n a
  change origin + n ≤ _ ∧ _ at hb
  have hroom : greedyStop origin n a < 2 ^ w := r.room
  have hf := r.old.laneFits (by omega : origin < 2 ^ w)
  constructor
  · intro x
    rw [column, r.color_at]
    apply Nat.mod_eq_of_lt
    exact ((orderedDyadicPacking X.slots X.baseIndex).color x).isLt.trans_le (Nat.succ_le_of_lt hc)
  · intro x
    rw [column, r.offset_at, tagWord_val]
  · intro x i
    change (r.post (T.baseOut + IncidenceDirectory.basePort X (x,i)).val).val = _
    rw [r.incidence.baseOut, IncidenceDirectory.basePort_number, Shrink.join, ← IncidenceDirectory.baseOrder_val]
    exact Nat.mod_eq_of_lt ((IncidenceDirectory.baseOrder X _).isLt.trans_le (r.old.baseFits.trans (by omega)))
  · intro x i
    change (r.post (T.shift + IncidenceDirectory.basePort X (x,i)).val).val = _
    rw [r.incidence.shift]
    exact Nat.mod_eq_of_lt ((bitWordFinEquiv _ _).isLt.trans_le (Nat.pow_le_pow_right (by decide) hf))


/-- Build the native color and offset setup in arbitrary scratch memory. The
input comprises exactly the old represented incidence table and the fresh range. -/
theorem build (X : ShrinkingState a g) (T : IncidenceDirectory w) (origin : ℕ) (m : Memory w)
    (rep : T.Represents X m) (old : OldBelow X T origin)
    (room : greedyStop origin (Fintype.card X.Base) a < 2 ^ w) : Nonempty (Run X T origin m) := by
  let n := Fintype.card X.Base
  let L := colorLayout w origin n a room
  let K := tagLayout w origin n a room
  let C := colorTables T origin n a
  let U := tagTables T origin n a
  let dst := CursorRAM.encode w (shiftBase origin n a)
  let zero := CursorRAM.encode w (zeroCell origin n a)
  let projected := projectedMemory X T origin m
  have hb := bounds origin n a
  change origin + n ≤ _ ∧ _ at hb
  change greedyStop origin n a < 2 ^ w at room
  have hr : origin < 2 ^ w := by omega
  have colorFit := colorFits origin n a w Fintype.card_pos room
  have degreeFit : 2 ^ a < 2 ^ w := by omega
  have baseFit := old.baseFits.trans hr.le
  have laneFit := old.laneFits hr
  have hw := (ShrinkTagColumn.radices_fit laneFit).2.2
  obtain ⟨projRun, projectedSlots⟩ := ShrinkTagColumn.extract_directory X T dst zero m rep laneFit (region X T origin old room)
  have preBelow : ∀ z < origin, projected z = m z :=
    fun z hz => projection_frame X T origin m room projRun z (by change z < shiftBase origin n a; omega)
  have preRep := old.preserve rep preBelow
  have hsC : L.limit < 2 ^ w := by change offsetBase origin n a < 2 ^ w; omega
  obtain ⟨colors⟩ := assignment_exists L C X.slots.base X.baseIndex (colorOperandRows (2 ^ a)) 1 (2 * 2 ^ a) projected
    (fun v : Fin (Shrink.colors a) => CursorRAM.encode w v.val) ((orderedDyadicPacking X.slots X.baseIndex).color) rfl
    (tables_rep preRep _ _ _ degreeFit baseFit) hsC (old.graphOutside L le_rfl _ _ _)
    (fun i => rowWords_color_length _ _ _ _) (WalkLayout.color_read_prepared L C X.slots.base X.baseIndex projected rfl colorFit)
  have colorBelow : ∀ z < origin, colors.post z = m z :=
    fun z hz => (colors.frame z (.inl hz)).trans (preBelow z hz)
  have hsK : K.limit < 2 ^ w := by change shiftBase origin n a < 2 ^ w; omega
  have zval : zero.val = zeroCell origin n a := Nat.mod_eq_of_lt (Nat.lt_of_succ_lt room)
  have zfar : K.limit ≤ zero.val := by rw [zval]; change shiftBase origin n a ≤ shiftBase origin n a + _; omega
  have sfar (e : X.Base × Fin (2 ^ a)) : K.limit ≤ (dst + IncidenceDirectory.basePort X e).val := by
    rw [shifted_port X origin room e]; change shiftBase origin n a ≤ shiftBase origin n a + _; omega
  have kl : L.limit ≤ K.limit := by change offsetBase origin n a ≤ shiftBase origin n a; omega
  have data : WalkLayout.OffsetData K U X.baseIndex hw (projectedTag X) colors.post := by
    constructor
    · exact (colors.frame zero.val (.inr (kl.trans zfar))).trans projRun.zero
    · exact Or.inr zfar
    · intro e
      exact (colors.frame _ (.inr (kl.trans (sfar e)))).trans (projectedSlots e)
    · exact fun e => Or.inr (sfar e)
  have hcard := packingTagBits_sufficient (2 ^ a)
  obtain ⟨offsets⟩ := assignment_exists K U X.slots.base X.baseIndex (tagOperandRows (2 ^ a)) 4
    (WalkLayout.tagCount (2 ^ a)) colors.post (tagWord hw) ((orderedDyadicPacking X.slots X.baseIndex).offset)
    rfl (tables_rep (old.preserve rep colorBelow) _ _ _ degreeFit baseFit) hsK
    (old.graphOutside K (by change origin ≤ offsetBase origin n a; omega) _ _ _)
    (fun i => by rw [rowWords_tag_length, tagTests_length, Nat.mul_comm])
    (WalkLayout.tag_read_prepared K U X.slots.base X.baseIndex colors.post rfl (projectedTag X) hw hcard data)
  exact ⟨⟨room, old, rep, hw, projRun, colors, offsets⟩⟩


namespace Run

variable {X : ShrinkingState a g} {T : IncidenceDirectory w} {origin : ℕ} {m : Memory w} (r : Run X T origin m)

/-- Chronological reports of the two tag-extraction visits, the color setup and
reader, and the tag setup and reader. -/
def reports : List (Report w) :=
  ShrinkTagColumn.reports (projectionWords T origin (Fintype.card X.Base) a g)
    (Fintype.card X.Base * 2 ^ a) m ++ r.color.prep ++ r.color.reads ++ r.offsets.prep ++ r.offsets.reads

theorem post_reports : after m (eventLog r.reports) = r.post := by
  simp only [reports, eventLog, List.flatMap_append, after, List.foldl_append]
  rfl

theorem reports_length : r.reports.length = Fintype.card X.Base * (2 ^ a + 4) + 1 := by
  simp only [reports, List.length_append, r.projection.calls, r.color.prepLength, r.color.readLength,
    r.offsets.prepLength, r.offsets.readLength]
  ring

private theorem readCost {N width degree : ℕ} {L : WalkLayout w N width} {V A : Type*} {U : PortTables w}
    {G : SlotGraph V degree} {order : V ≃ Fin N} {rows : OperandRows degree} {arity tests : ℕ}
    {src : Memory w} {encode : A → Word w} {f : V → A} (P : Assignment L U G order rows arity tests src encode f) :
    RAMBuckets.cost Report.probes P.reads = N * (4 + 2 * arity * tests * tests) := by
  have h (rs : List (Report w)) (hw : ∀ r ∈ rs, r.probes = 3 + 2 * arity * tests * tests) :
      RAMBuckets.cost Report.probes rs = rs.length * (4 + 2 * arity * tests * tests) := by
    induction rs with
    | nil => simp [RAMBuckets.cost]
    | cons r rs ih =>
      rw [RAMBuckets.cost, hw r List.mem_cons_self, ih (fun s hs => hw s (List.mem_cons_of_mem _ hs))]
      simp only [List.length_cons, Nat.succ_mul]
      omega
  rw [h _ (fun z hz => (P.readWork z hz).2), P.readLength]

/-- Total native calls plus probes depend linearly on the number of base
vertices for each of the fixed degrees used by the compressor. -/
theorem reports_cost :
    let d := 2 ^ a
    let t := WalkLayout.tagCount d
    RAMBuckets.cost Report.probes r.reports =
      2 + Fintype.card X.Base * (16 + 7*d + 8*d^2 + 5*t + 8*t^2) := by
  simp only [reports, RAMBuckets.cost_append, r.projection.cost, r.color.prepCost, readCost,
    r.offsets.prepCost, colorOperandRows, tagOperandRows, List.length_map, incidences_length,
    tagTests_length, WalkLayout.tagCount]
  ring

end Run

theorem greedyStop_eq (origin n a : ℕ) :
    greedyStop origin n a = origin + n * (6 + 3 * 2 ^ a + 4 * WalkLayout.tagCount (2 ^ a)) + 1 := by
  unfold greedyStop zeroCell shiftBase offsetBase
  ring

end CompressorRecords.GreedyArena

end VPVNP
end Computability
end OAI
