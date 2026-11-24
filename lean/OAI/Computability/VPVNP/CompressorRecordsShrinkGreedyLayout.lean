import OAI.Computability.VPVNP.CompressorRecordIncidenceLayout
import OAI.Computability.VPVNP.CompressorRecordsShrink
import OAI.Computability.VPVNP.CompressorRecordGreedyPass

/-!
# Fresh storage for the shrinking step's color and tag assignments

Both directed mate arrays and the original lane displacement stay in the
input incidence directory. New storage contains the two complete assignment
directories, one projected tag per outgoing base port, and a shared zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.GreedyArena

open BurstRAM Compression Greedy

/-- The origin of the greedy color assignment's fresh storage. -/
def colorBase (origin : ℕ) := origin
/-- The first address after the color walk's labels and work rows, where the tag-offset walk
begins. -/
def offsetBase (origin n a : ℕ) := origin + n + n * (2 + 2 * 2 ^ a)
/-- The first address after both greedy walk regions, reserved for the projected displacements
of old base ports. -/
def shiftBase (origin n a : ℕ) := offsetBase origin n a + n + n * (2 + 4 * WalkLayout.tagCount (2 ^ a))
/-- The shared zero operand stored immediately after the projected displacement column. -/
def zeroCell (origin n a : ℕ) := shiftBase origin n a + n * 2 ^ a
/-- The exclusive upper bound of the greedy assignment workspace, one word past its zero
operand. -/
def greedyStop (origin n a : ℕ) := zeroCell origin n a + 1

theorem bounds (origin n a : ℕ) :
    colorBase origin + n ≤ offsetBase origin n a ∧ offsetBase origin n a + n ≤ shiftBase origin n a ∧
      shiftBase origin n a + n * 2 ^ a < greedyStop origin n a := by
  simp only [colorBase, greedyStop, zeroCell, shiftBase, offsetBase]
  omega

/-- The bounded layout of the greedy color walk, with room for the two directed incidences at
each slot. -/
def colorLayout (w origin n a : ℕ) (room : greedyStop origin n a < 2 ^ w) : WalkLayout w n (2 * 2 ^ a) :=
  ⟨colorBase origin, by change offsetBase origin n a ≤ 2 ^ w; have := bounds origin n a; omega⟩

/-- The bounded layout of the greedy offset walk, using its four tag-count groups per work row. -/
def tagLayout (w origin n a : ℕ) (room : greedyStop origin n a < 2 ^ w) :
    WalkLayout w n (4 * WalkLayout.tagCount (2 ^ a)) :=
  ⟨offsetBase origin n a, by change shiftBase origin n a ≤ 2 ^ w; have := bounds origin n a; omega⟩

@[simp] theorem color_limit (w origin n a : ℕ) (h : greedyStop origin n a < 2 ^ w) :
    (colorLayout w origin n a h).limit = offsetBase origin n a := rfl

@[simp] theorem tag_limit (w origin n a : ℕ) (h : greedyStop origin n a < 2 ^ w) :
    (tagLayout w origin n a h).limit = shiftBase origin n a := rfl

variable {w a l : ℕ}

/-- The six old columns are below the beginning of the new scratch range. -/
def OldBelow (X : State a l) (T : IncidenceDirectory w) (origin : ℕ) : Prop :=
  ∀ c : Fin 6, (T.column c).val + Fintype.card X.Base * 2 ^ l * 2 ^ a ≤ origin

private theorem basePort_lt (X : State a l) (e : X.Base × Fin (2 ^ a)) :
    (IncidenceDirectory.basePort (w := w) X e).val < Fintype.card X.Base * 2 ^ l * 2 ^ a := by
  rw [IncidenceDirectory.basePort_number]
  have h := (IncidenceDirectory.baseOrder X e).isLt
  exact (Nat.mod_le _ _).trans_lt (h.trans_le (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos l))))

private theorem actualPort_lt (X : State a l) (e : (X.Base × BitWord l) × Fin (2 ^ a)) :
    (IncidenceDirectory.actualPort (w := w) X e).val < Fintype.card X.Base * 2 ^ l * 2 ^ a := by
  rw [IncidenceDirectory.actualPort_number]
  exact (Nat.mod_le _ _).trans_lt (IncidenceDirectory.actualOrder X e).isLt

theorem OldBelow.cell {X : State a l} {T : IncidenceDirectory w} {origin : ℕ}
    (h : OldBelow X T origin) (c : Fin 6) (j : Word w)
    (hj : j.val < Fintype.card X.Base * 2 ^ l * 2 ^ a) : (T.column c + j).val < origin := by
  rw [Fin.val_add]
  exact (Nat.mod_le _ _).trans_lt (Nat.add_lt_add_left hj _ |>.trans_le (h c))

theorem OldBelow.preserve {X : State a l} {T : IncidenceDirectory w} {origin : ℕ}
    {m post : Memory w} (h : OldBelow X T origin) (rep : T.Represents X m)
    (frame : ∀ z < origin, post z = m z) : T.Represents X post := by
  constructor
  · intro e; exact (frame _ (h.cell 0 _ (basePort_lt X e))).trans (rep.baseOut e)
  · intro e; exact (frame _ (h.cell 1 _ (basePort_lt X e))).trans (rep.baseIn e)
  · intro e; exact (frame _ (h.cell 2 _ (basePort_lt X e))).trans (rep.shift e)
  · intro e; exact (frame _ (h.cell 3 _ (actualPort_lt X e))).trans (rep.actualOut e)
  · intro e; exact (frame _ (h.cell 4 _ (actualPort_lt X e))).trans (rep.actualIn e)
  · intro e; exact (frame _ (h.cell 5 _ (actualPort_lt X e))).trans (rep.width e)

theorem OldBelow.fit {X : State a l} {T : IncidenceDirectory w} {origin : ℕ} (old : OldBelow X T origin) :
    Fintype.card X.Base * 2 ^ l * 2 ^ a ≤ origin := by have := old 0; omega

/-- Assemble the walker's port tables from the old incidence directory and the specified label,
zero, and displacement columns. -/
def tables (T : IncidenceDirectory w) (a : ℕ) (labels zero disps : Word w) : PortTables w :=
  { T.greedyTables a labels zero with displacements := disps }

theorem tables_rep {X : State a l} {T : IncidenceDirectory w} {m : Memory w} (rep : T.Represents X m)
    (labels zero disps : Word w) (degree : 2 ^ a < 2 ^ w) (baseFits : Fintype.card X.Base * 2 ^ a ≤ 2 ^ w) :
    (tables T a labels zero disps).Represents X.slots.base X.baseIndex m := by
  have h := rep.greedy labels zero degree baseFits
  exact ⟨h.degree,h.fits,h.vertices,h.outgoing,h.incoming⟩

theorem OldBelow.graphOutside {X : State a l} {T : IncidenceDirectory w} {origin width : ℕ}
    (h : OldBelow X T origin) (L : WalkLayout w (Fintype.card X.Base) width) (hle : origin ≤ L.origin)
    (labels zero disps : Word w) : GraphOutside (d := 2 ^ a) L (tables T a labels zero disps) X.baseIndex := by
  intro e b hb
  change b ∈ [T.baseOut,T.baseIn] at hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact Or.inl ((h.cell 0 _ (basePort_lt X e)).trans_le hle)
  · obtain rfl := List.mem_singleton.mp hb
    exact Or.inl ((h.cell 1 _ (basePort_lt X e)).trans_le hle)


theorem OldBelow.baseFits {X : State a l} {T : IncidenceDirectory w} {origin : ℕ}
    (old : OldBelow X T origin) : Fintype.card X.Base * 2 ^ a ≤ origin :=
  (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos l))).trans old.fit

theorem OldBelow.laneFits {X : State a l} {T : IncidenceDirectory w} {origin : ℕ}
    (old : OldBelow X T origin) (room : origin < 2 ^ w) : l ≤ w := by
  have npos : 0 < Fintype.card X.Base := Fintype.card_pos
  have h : 2 ^ l ≤ origin :=
    (Nat.le_mul_of_pos_left _ npos).trans ((Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a)).trans old.fit)
  exact Nat.le_of_not_gt fun bad => (Nat.pow_lt_pow_right (by decide : 1 < 2) bad).not_ge (h.trans room.le)

theorem colorFits (origin n a w : ℕ) (npos : 0 < n) (room : greedyStop origin n a < 2 ^ w) :
    2 * 2 ^ a < 2 ^ w := by
  have h : 2 + 2 * 2 ^ a ≤ n * (2 + 2 * 2 ^ a) := Nat.le_mul_of_pos_left _ npos
  have := bounds origin n a
  unfold offsetBase at *
  omega

end CompressorRecords.GreedyArena

end VPVNP
end Computability
end OAI
