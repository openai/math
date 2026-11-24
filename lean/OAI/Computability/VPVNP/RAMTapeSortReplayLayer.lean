import OAI.Computability.VPVNP.RAMTapeSortReplayRow
import OAI.Computability.VPVNP.RAMTapeSortLayerRowsModel

/-! # One materialized sorting layer agrees with the checked RAM replay

The machine compares arbitrary fixed-width record fields. Its initially
canonical local block supplies the left operand at every row. If every
new row flag passes, the next block is canonical and parses to the checked
replay's next block. The acceptance test also covers malformed incident fields.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortReplay

open BurstRAM RAMMemory RAMSort RAMBoundary SortLayerRows

variable {h d w : ℕ}

/-- The current block of raw five-word rows and the accumulated Boolean validity flags of the
physical replay. -/
abbrev State (h w : ℕ) := Wires h (RawSlot w) × List Bool

/-- Replay one bitonic stage using its incident send and receive fields, replacing the local
block by the selected rows and accumulating their checks. -/
def update (raw : ℕ → Bool) (v : Word d) (x : State h w) (s : Stage (h+d)) : State h w :=
  let send := fieldWords w raw s 0
  let recv := fieldWords w raw s 1
  (selected s v x.1 recv, (List.ofFn (SortLayerRows.checks s x.1 send recv)).reverse.flatten ++ x.2)

/-- Parse every raw five-word row in a physical block to the ordered slot used in the checked
sorting replay. -/
abbrev decoded (hw : 2 ≤ w) (x : Wires h (RawSlot w)) : Wires h (OrderedSlot (Word w)) :=
  fun i => parsedSlot hw (x i)

/-- Each raw row of this block is exactly the canonical encoding of its parsed slot. -/
abbrev CanonicalBlock (hw : 2 ≤ w) (x : Wires h (RawSlot w)) := ∀ i, Canonical hw (x i)

private theorem checks_row (hw : 2 ≤ w) (raw : ℕ → Bool) (s : Stage (h+d)) (v : Word d)
    (cur : Wires h (RawSlot w)) (hcur : CanonicalBlock hw cur) (i : Word h) :
    (SortLayerRows.checks s cur (fieldWords w raw s 0) (fieldWords w raw s 1) i).all id = true ↔
      (scanRow hw raw s v (decoded hw cur) i).ok = true := by
  by_cases hc : s.stride < h
  · rw [local_ok hw raw s v _ i hc]
    simp only [SortLayerRows.checks, other, hc, ite_true, List.all_cons, List.all_nil,
      id_eq, Bool.and_true, selectOK_iff hw]
    exact ⟨fun _ => trivial, fun _ => ⟨hcur _, hcur _⟩⟩
  · rw [cross_ok hw raw s v _ i (Nat.le_of_not_gt hc)]
    simp only [SortLayerRows.checks, other, hc, ite_false, List.all_cons, List.all_nil,
      id_eq, Bool.and_true, Bool.and_eq_true, selectOK_iff hw, verifyOK_iff hw]
    constructor
    · rintro ⟨⟨_, hi⟩, ⟨_, ho⟩, he⟩
      exact ⟨ho, hi, congrArg (parsedSlot hw) he.symm⟩
    · rintro ⟨ho, hi, he⟩
      exact ⟨⟨hcur i, hi⟩, ⟨hcur i, ho⟩, ((parsed_eq_iff hw ho (hcur i)).mp he).symm⟩

private theorem accepted_row (hw : 2 ≤ w) (raw : ℕ → Bool) (s : Stage (h+d)) (v : Word d)
    (cur : Wires h (RawSlot w)) (i : Word h)
    (hp : (SortLayerRows.checks s cur (fieldWords w raw s 0) (fieldWords w raw s 1) i).all id = true) :
    let result := selected s v cur (fieldWords w raw s 1) i
    Canonical hw result ∧ parsedSlot hw result = (scanRow hw raw s v (decoded hw cur) i).slot := by
  have hsel := (selectOK_iff hw ..).mp (Bool.and_eq_true_iff.mp hp).1
  refine ⟨chosen_canonical hw _ hsel.1 hsel.2, ?_⟩
  by_cases hc : s.stride < h
  · rw [local_value hw raw s v _ i hc]
    simp only [selected, parsed_chosen, other, hc, ite_true, peerIndex, dite_true, keepMin]
  · have hi : Canonical hw (fieldWords w raw s 1 i) := by simpa only [other, hc, ite_false] using hsel.2
    rw [cross_value hw raw s v _ i (Nat.le_of_not_gt hc) hi]
    simp only [selected, parsed_chosen, other, hc, ite_false, keepMin]

private theorem all_rows {α : Type} {n : ℕ} (f : Fin n → α) (p : α → Bool) :
    (List.ofFn f).all p = true ↔ ∀ i, p (f i) = true := by
  simp [List.all_eq_true, List.mem_ofFn]

private theorem new_flags (hw : 2 ≤ w) (raw : ℕ → Bool) (s : Stage (h+d)) (v : Word d)
    (cur : Wires h (RawSlot w)) (hcur : CanonicalBlock hw cur) :
    (List.ofFn (SortLayerRows.checks s cur (fieldWords w raw s 0) (fieldWords w raw s 1))).reverse.flatten.all id =
      (scanLayer hw raw s v (decoded hw cur)).ok := by
  apply Bool.eq_iff_iff.mpr
  rw [List.all_flatten, List.all_reverse, all_rows]
  simp only [scanLayer, Vector.getElem_ofFn, all_rows, id_eq]
  exact forall_congr' (checks_row hw raw s v cur hcur)

/-- Existing failure flags are retained even when this layer sees arbitrary bits. -/
theorem update_retains (raw : ℕ → Bool) (v : Word d) (x : State h w) (s : Stage (h+d))
    (hp : (update raw v x s).2.all id = true) : x.2.all id = true := by
  simp only [update, List.all_append, Bool.and_eq_true] at hp
  exact hp.2

theorem update_flags (hw : 2 ≤ w) (raw : ℕ → Bool) (v : Word d) (x : State h w)
    (s : Stage (h+d)) (hcur : CanonicalBlock hw x.1) :
    (update raw v x s).2.all id =
      (x.2.all id && (scanLayer hw raw s v (decoded hw x.1)).ok) := by
  simp only [update, List.all_append, new_flags hw raw s v x.1 hcur]
  exact Bool.and_comm ..

theorem update_output (hw : 2 ≤ w) (raw : ℕ → Bool) (v : Word d) (x : State h w)
    (s : Stage (h+d)) (hp : (update raw v x s).2.all id = true) :
    CanonicalBlock hw (update raw v x s).1 ∧
      decoded hw (update raw v x s).1 = (scanLayer hw raw s v (decoded hw x.1)).block := by
  simp only [update, List.all_append, Bool.and_eq_true, List.all_flatten, List.all_reverse, all_rows] at hp
  have rows := fun i => accepted_row hw raw s v x.1 i (hp.1 i)
  exact ⟨fun i => (rows i).1, funext fun i => by simp only [scanLayer, Vector.getElem_ofFn, update, decoded]; exact (rows i).2⟩

end RAMTape.SortReplay

end VPVNP
end Computability
end OAI
