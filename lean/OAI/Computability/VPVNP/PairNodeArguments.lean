import OAI.Computability.VPVNP.PairSimulationPrivateFields
import OAI.Computability.VPVNP.PairSimulationHistoryBounds
import OAI.Computability.VPVNP.CompressorRecordIncidenceLayout

/-!
# The private argument buffer for a descriptor node

One contiguous interval per node holds its outgoing half-wire bits followed
by its incoming half-wire bits. An incoming slot looks up the width of the
matched outgoing arc. The two half-wires are independent in a child guess,
including when the graph has parallel arcs or loops. A child later reads
exactly the private words that its parent filled.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments

open BurstRAM BurstRAM.PrivateRAM Compression LocalHistory CompressorRecords
open scoped Fin.CommRing

/-- The private argument interval of a node is indexed by its absolute DFS address. -/
structure Arena where
  /-- Private memory address from which the per-node half-wire argument intervals are
  allocated. -/
  start : ℕ
  /-- Distance in private words between the starts of argument intervals for consecutive
  descriptor addresses. -/
  stride : ℕ

/-- Starting address of the private argument interval for an absolute descriptor address,
obtained by scaling the address by the arena stride. -/
def Arena.base (A : Arena) (node : ℕ) : ℕ := A.start + node * A.stride

theorem Arena.before (A : Arena) {n m : ℕ} (h : n < m) : A.base n + A.stride ≤ A.base m := by
  unfold base
  have hmul := Nat.mul_le_mul_right A.stride h
  rw [Nat.succ_mul] at hmul
  omega

theorem Arena.disjoint (A : Arena) {n m : ℕ} (h : n ≠ m) :
    A.base n + A.stride ≤ A.base m ∨ A.base m + A.stride ≤ A.base n :=
  (lt_or_gt_of_ne h).imp A.before A.before

variable {a g : ℕ} (X : State a g) (u : X.network.Site)

/-- The actual slot field as seen by the old vertex, independently at each end. -/
noncomputable def fieldBits (h : X.network.Half u) (dir : Bool) (j : Fin (2 ^ a)) :
    Fin (X.halfWidth u dir j) → Bool :=
  match dir with
  | false => let e := (outgoingOrder X u).entries j; h.1 e.val e.property
  | true => let e := (incomingOrder X u).entries j; h.2 e.val e.property

/-- The half-wire bit strings at site `u` in numbered slot order, using outgoing arcs for
`false` and incoming arcs for `true`. -/
noncomputable def fields (h : X.network.Half u) (dir : Bool) : List (List Bool) :=
  List.ofFn fun j ↦ List.ofFn (fieldBits X u h dir j)

/-- Concatenation used both when a parent guesses a child and at its later visit. -/
noncomputable def packed (h : X.network.Half u) : List Bool :=
  (fields X u h false).flatten ++ (fields X u h true).flatten

private theorem fiber_encode {I V : Type} {B : I → Type} (p : I → V) (v : V)
    (o : Order {i // v = p i}) (r : ∀ i, ChoiceReader (B i)) (h : NetworkKernel.Placed p B v) :
    ((fiber p v o r).encode h) =
      (List.ofFn fun j ↦ (r (o.entries j).val).encode
        (h (o.entries j).val (o.entries j).prop)).flatten := by
  unfold fiber Order.reader ChoiceReader.reindex
  dsimp only
  rw [ChoiceReader.vector_encode]
  rfl

/-- The concrete RAM byte order agrees with the abstract traversal's old-half parser. -/
theorem packed_eq_encode (h : X.network.Half u) : packed X u h =
    ((half X.network u (outgoingOrder X u) (incomingOrder X u) (statePayload X)).encode h) := by
  change _ = _ ++ _
  rw [fiber_encode, fiber_encode]
  unfold packed fields
  congr 2 <;> congr 1 <;> funext j <;> exact (PrivateFields.bitField_encode _).symm

theorem packed_length (h : X.network.Half u) :
    (packed X u h).length = ∑ dir : Bool, ∑ j, X.halfWidth u dir j := by
  rw [packed_eq_encode, stateHalf_length]

/-- Slot offset uses widths only and has no dependence on the guessed values. -/
noncomputable def offset (dir : Bool) (j : Fin (2 ^ a)) : ℕ :=
  (if dir then ∑ t, X.halfWidth u false t else 0) +
    ((List.ofFn (X.halfWidth u dir)).take j.val).sum

/-- Start of a numbered half-wire field within a node's private interval. Incoming fields
follow the entire outgoing block, and earlier fields contribute their widths. -/
noncomputable def Arena.fieldAddress (A : Arena) (node : ℕ) (dir : Bool) (j : Fin (2 ^ a)) : ℕ :=
  A.base node + offset X u dir j

private theorem fields_offset (h : X.network.Half u) (dir : Bool) (j : Fin (2 ^ a)) :
    ((fields X u h dir).take j.val).flatten.length =
      ((List.ofFn (X.halfWidth u dir)).take j.val).sum := by
  simp [fields, Function.comp_def]

private theorem fields_size (h : X.network.Half u) (dir : Bool) :
    (fields X u h dir).flatten.length = ∑ j, X.halfWidth u dir j := by
  simp [fields, List.length_flatten, List.sum_ofFn]

/-- Each endpoint's declared slot is precisely its slice of the private buffer. -/
theorem packed_member (h : X.network.Half u) (dir : Bool) (j : Fin (2 ^ a)) :
    ∃ before after : List Bool, packed X u h = before ++
      List.ofFn (fieldBits X u h dir j) ++ after ∧
      before.length = offset X u dir j := by
  let rows := fields X u h dir
  let start := (rows.take j.val).flatten
  let stop := (rows.drop (j.val+1)).flatten
  have hj : j.val < rows.length := by simp [rows,fields]
  have hr : rows.flatten = start ++ List.ofFn (fieldBits X u h dir j) ++ stop := by
    have he := (List.take_append_drop j.val rows).symm
    rw [List.drop_eq_getElem_cons hj] at he
    have hf := congrArg List.flatten he
    simpa [rows, fields, start, stop, List.append_assoc] using hf
  cases dir with
  | false =>
    exact ⟨start, stop ++ (fields X u h true).flatten, by
      change _ ++ _ = _; rw [hr]; simp [List.append_assoc], by
      simpa [offset,start,rows] using fields_offset X u h false j⟩
  | true =>
    exact ⟨(fields X u h false).flatten ++ start, stop, by
      change _ ++ _ = _; rw [hr]; simp [List.append_assoc], by
      rw [List.length_append, fields_size, show start.length = _ from fields_offset X u h true j]
      simp [offset]⟩

/-- Guessing the whole child buffer supplies each individual native slot at its
calculated private address and preserves private words outside the interval. -/
theorem stored_member {w : ℕ} (A : Arena) (node : ℕ) (h : X.network.Half u)
    (mem : Word w → Word w) (fit : A.base node + (packed X u h).length ≤ 2 ^ w)
    (dir : Bool) (j : Fin (2 ^ a)) (i : Fin (X.halfWidth u dir j)) :
    PrivateFields.storeBits (A.base node) (packed X u h) mem
      ((A.fieldAddress X u node dir j + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w (fieldBits X u h dir j i) := by
  obtain ⟨pre,post,he,hoff⟩ := packed_member X u h dir j
  have hlen : pre.length + i.val < (packed X u h).length := by rw [he]; simp; omega
  have hb := PrivateFields.storeBits_read (A.base node) _ mem fit ⟨pre.length+i.val, hlen⟩
  rw [Arena.fieldAddress, ← hoff, Nat.add_assoc]
  refine hb.trans ?_
  change PrivateFields.bitValue w (packed X u h)[pre.length+i.val] = _
  simp [he, i.isLt]

namespace WidthRead

/-- External address of the selected width. Incoming fields use the inverse slot
column before addressing the old width array. -/
def value {w : ℕ} (T : IncidenceDirectory w) (m : Memory w) (dir : Bool) (port : Word w) :=
  let id := if dir then m (T.actualIn + port).val else port
  m (T.width + id).val

/-- A concrete field header reads the old forward width or the width at the
original source of the incoming half, retaining all slot multiplicities. -/
theorem value_actual {w : ℕ} (T : IncidenceDirectory w) (mem : Memory w)
    (rep : T.ActualColumns X mem) (dir : Bool) (j : Fin (2 ^ a)) :
    value T mem dir (IncidenceDirectory.actualPort X (u,j)) =
      CursorRAM.encode w (X.halfWidth u dir j) := by
  cases dir with
  | false => exact rep.width _
  | true => simp only [value, ite_true, rep.actualIn]; exact rep.width _

end WidthRead
end PairSimulation.NodeArguments

end VPVNP
end Computability
end OAI
