import OAI.Computability.VPVNP.CompressorRecordsShrinkGreedy

/-!
# Addresses stored in the color and offset operand records

The color records point to labels in their own arena. The offset records
point to offset labels, projected displacements or the common zero cell.
All of these lie in the newly allocated greedy region.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.GreedyArena

open BurstRAM Compression Greedy
open scoped Fin.CommRing

private theorem tagPointers_range {V : Type*} {w d : ℕ} (rd : ℕ → Prop) (G : SlotGraph V d)
    (A : TagAddresses V d w) (x : V) (t : SlotGraph.TagTests d)
    (zero : rd A.zero.val) (disp : ∀ e, rd (A.displacement e).val) (label : ∀ x, rd (A.label x).val) :
    ∀ u ∈ tagPointers G A x t, rd u.val := by
  have incr (y : V) (i : Option (Fin d)) : rd (A.increment y i).val := by
    cases i with
    | none => exact zero
    | some i => exact disp (y,i)
  obtain ⟨⟨b,i⟩,j | ⟨j,k⟩⟩ := t <;> cases b
  all_goals
    intro u hu
    simp only [tagPointers,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl <;> first | exact zero | exact disp _ | exact incr _ _ | exact label _

namespace Run

variable {w a g origin : ℕ} {X : ShrinkingState a g} {T : IncidenceDirectory w}
    {m : Memory w} (r : Run X T origin m)
local notation "n" => Fintype.card X.Base
local notation "L" => colorLayout w origin n a r.room
local notation "K" => tagLayout w origin n a r.room

open private assignment_addresses from OAI.Computability.VPVNP.CompressorRecordGreedyPass
open private shifted_port from OAI.Computability.VPVNP.CompressorRecordsShrinkGreedy
include r

/-- Every color operand is the address of a label in the fresh color array. -/
theorem color_pointer_range (x : X.Base) (u : Word w)
    (hu : u ∈ rowWords (colorTables T origin n a) X.slots.base X.baseIndex x (colorOperandRows (2^a))) :
    origin ≤ u.val ∧ u.val < origin+n := by
  rw [rowWords_color, assignment_addresses (d := 2^a) L _ _ rfl] at hu
  obtain ⟨z, hz, huz⟩ := List.mem_flatten.mp hu
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hz
  obtain rfl := List.mem_singleton.mp huz
  change origin ≤ ((L).label _).val ∧ ((L).label _).val < origin+n
  rw [WalkLayout.label_val]
  exact ⟨Nat.le_add_right .., Nat.add_lt_add_left (X.baseIndex _).isLt _⟩

/-- Every offset operand points to an offset label, a projected displacement
word or the common zero word, all within the same fresh allocation. -/
theorem tag_pointer_range (x : X.Base) (u : Word w)
    (hu : u ∈ rowWords (tagTables T origin n a) X.slots.base X.baseIndex x (tagOperandRows (2^a))) :
    origin ≤ u.val ∧ u.val < greedyStop origin n a := by
  rw [rowWords_tag] at hu
  obtain ⟨z, hz, huz⟩ := List.mem_flatten.mp hu
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hz
  have hb := bounds origin n a
  change origin+n ≤ _ ∧ _ at hb
  have room := r.room
  apply tagPointers_range (fun v ↦ origin ≤ v ∧ v < greedyStop origin n a) _ _ _ _ _ _ _ _ huz
  · change origin ≤ zeroCell origin n a % (2^w) ∧ zeroCell origin n a % (2^w) < greedyStop origin n a
    rw [Nat.mod_eq_of_lt (Nat.lt_of_succ_lt room)]
    change origin ≤ shiftBase origin n a+n*2^a ∧ shiftBase origin n a+n*2^a < greedyStop origin n a
    omega
  · intro e
    change origin ≤ (CursorRAM.encode w (shiftBase origin n a) + IncidenceDirectory.basePort X e).val ∧
      (CursorRAM.encode w (shiftBase origin n a) + IncidenceDirectory.basePort X e).val < greedyStop origin n a
    rw [shifted_port X origin room e]
    have he := (IncidenceDirectory.baseOrder X e).isLt
    change _ < n*2^a at he
    omega
  · intro y
    rw [assignment_addresses (d := 2^a) K _ _ rfl]
    simp only [Function.comp_apply, WalkLayout.label_val]
    have hy := (X.baseIndex y).isLt
    change origin ≤ offsetBase origin n a + (X.baseIndex y).val ∧ offsetBase origin n a + (X.baseIndex y).val < greedyStop origin n a
    omega

end Run

end CompressorRecords.GreedyArena

end VPVNP
end Computability
end OAI
