import OAI.Computability.VPVNP.PairNodeArguments
import OAI.Computability.VPVNP.CompressorRecordsCursorCoordinates
import OAI.Computability.VPVNP.SlotDemandSlices
import Mathlib.Data.Fin.Tuple.Take

/-!
# The four actual argument vectors at a cursor leaf

Outgoing slot zero is the stay arc and slot one is the flip arc. The
incoming slots retain these same numbers at their destinations. Each
genuine arc concatenates the successor fields and then the sorting
fields in the order used by the validator. The dummy arcs have width
zero, so the four vectors occupy four consecutive private intervals.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafArguments

open Compression CursorNetwork CursorRouting RAMLayout RAMSort NodeArguments LocalHistory
open scoped Classical Fin.CommRing

variable {D H w : ℕ}

/-- Width of the numerical system column in the padded cursor arc. -/
private theorem column_width (j : Fin (D + layerCount D)) :
    ramFieldBits H w ((ramSystemOrder D).symm j) = if j.val < D then 8*w else blockBits H w := by
  obtain ⟨s,rfl⟩ := (ramSystemOrder D).surjective j
  rw [Equiv.symm_apply_apply]
  cases s with
  | inl i =>
    change 8*w = if i.val < D then _ else _
    rw [ite_eq_left i.isLt]
  | inr l =>
    change blockBits H w = if D + l.ordinal.val < D then _ else _
    rw [ite_eq_right (by omega)]

/-- Compression and the site validator number every bit of the actual
message systems identically. -/
theorem ordered_ram_offset (s : RAMSystem D) (i : Fin (ramFieldBits H w s)) :
    (PackingData.orderedBits (ramSystemOrder D) (ramFieldBits H w) ⟨s,i⟩).val =
      (ramFieldOffset D H w ⟨s,i⟩).val := by
  rw [PackingData.orderedBits_offset, PackingData.fieldStart]
  simp_rw [column_width]
  cases s with
  | inl j =>
    erw [ramFieldOffset_successor (H := H) j i]
    change (∑ t : Fin j.val, if t.val < D then 8*w else blockBits H w) + i.val = _
    simp [fun t : Fin j.val => t.isLt.trans j.isLt]
  | inr l =>
    erw [ramFieldOffset_sort (D := D) l i]
    change (∑ t : Fin (D + l.ordinal.val), if t.val < D then 8*w else blockBits H w) + i.val = _
    rw [Fin.sum_univ_add]
    simp [Fin.val_castAdd, Fin.val_natAdd]

variable {b l a p : ℕ} [NeZero (b+l)] (hD : 1 < b+l) (hd : 2+p=2^a)

private abbrev bits (H w : ℕ) := (ramFieldBits H w : RAMSystem (b+l) → ℕ)

/-- The padded compression state for the cursor graph, with base and lane coordinates and the
widths of the successor and sorting messages. -/
noncomputable abbrev state (H w : ℕ) := cursorState (cursorCoordinateLabels b l) hD hd (bits (b := b) (l := l) H w)
/-- Identify the padded cursor graph with its compression state, numbering payload bits in RAM
system order. -/
noncomputable abbrev iso (H w : ℕ) := cursorStateIso (cursorCoordinateLabels b l) hD hd (ramSystemOrder (b+l)) (bits (b := b) (l := l) H w)

/-- The padded slot index of the genuine stay or flip arc designated by the side bit. -/
def realSlot (hd : 2+p=2^a) (side : Bool) := finCongr hd (paddingSlots p (.inl side))

omit [NeZero (b+l)] in
private theorem width_real (e : Arc (b+l)) :
    (state hD hd H w).width ((((iso hD hd H w).edge (.inl e)).1.1, ((iso hD hd H w).edge (.inl e)).2),
      ((iso hD hd H w).edge (.inl e)).1.2) = ramPayloadWidth (b+l) H w := by
  change CursorNetwork.paddedWidth (bits (b := b) (l := l) H w) ((stateEdges (cursorCoordinateLabels b l) hd).symm (stateEdges (cursorCoordinateLabels b l) hd (.inl e))) = _
  rw [Equiv.symm_apply_apply]
  exact (ramPayloadWidth_eq_sum _ _ _).symm

omit [NeZero (b+l)] in
private theorem real_payload (e : Arc (b+l)) (y : Payload (bits (b := b) (l := l) H w)) :
    List.ofFn (((iso hD hd H w).payload (.inl e)) y) = List.ofFn (ramPayloadEquiv (b+l) H w y) := by
  refine (List.ofFn_congr (width_real hD hd e) (((iso hD hd H w).payload (.inl e)) y)).trans ?_
  apply congrArg List.ofFn
  funext j
  obtain ⟨⟨s,i⟩,rfl⟩ := (ramFieldOffset (b+l) H w).surjective j
  rw [ramPayloadEquiv_offset]
  let order := ramSystemOrder (b+l)
  let idx := PackingData.orderedBits order (bits (b := b) (l := l) H w)
  change ((Equiv.piCurry _).symm y) (idx.symm ⟨(ramFieldOffset _ _ _ ⟨s,i⟩).val, _⟩) = _
  let q := ramFieldOffset (b+l) H w ⟨s,i⟩
  let k : Fin (∑ s, bits (b := b) (l := l) H w s) := ⟨q.val, by
    rw [← ramPayloadWidth_eq_sum (b+l) H w]; exact q.isLt⟩
  have he : idx.symm k = ⟨s,i⟩ := idx.injective ((idx.apply_symm_apply k).trans (Fin.ext (ordered_ram_offset s i).symm))
  exact congrArg (fun t : (s : RAMSystem (b+l)) × Fin (ramFieldBits H w s) => y t.1 t.2) he

/-- The state's independent halves, interpreted in the padded cursor's
original coordinates. -/
noncomputable def buffers (v : Position (b+l)) (z : (state hD hd H w).network.Half (lanePositions (cursorCoordinateLabels b l) v)) :=
  halfBuffers v (unpadHalf p v ((iso hD hd H w).pullHalf v z))

theorem outgoing_bits (v : Position (b+l))
    (z : (state hD hd H w).network.Half (lanePositions (cursorCoordinateLabels b l) v)) (side : Bool) :
    List.ofFn (fieldBits (state hD hd H w) _ z false (realSlot hd side)) =
      List.ofFn (buffers hD hd v z (.outgoing side)) := by
  let I := iso hD hd H w
  let e : Arc (b+l) := (v.1,v.2,side)
  let val := z.1 (I.edge (.inl e)) rfl
  have h := real_payload hD hd e ((I.payload (.inl e)).symm val)
  rw [Equiv.apply_symm_apply] at h
  exact h

private theorem incoming_edge (v : Position (b+l)) (side : Bool) :
    ((incomingOrder (state hD hd H w) (lanePositions (cursorCoordinateLabels b l) v)).entries (realSlot hd side)).val =
      (iso hD hd H w).edge (.inl (incomingArc v side)) := by
  let I := iso hD hd H w
  let X := state hD hd H w
  let e := incomingArc v side
  let slot := realSlot hd side
  change X.slots.actualGraph.target.symm (I.site v, slot) = I.edge (.inl e)
  apply X.slots.actualGraph.target.injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · change I.site v = X.network.dst (I.edge (.inl e))
    exact (congrArg I.site (head_incomingArc v side).symm).trans (I.dst (.inl e))
  · rfl

private theorem incoming_congr {X : State a l} {u : X.network.Site} (z : X.network.Half u)
    {e e' : X.network.Edge} (he : e = e') (h : u = X.network.dst e) (h' : u = X.network.dst e') :
    List.ofFn (z.2 e h) = List.ofFn (z.2 e' h') := by cases he; rfl

theorem incoming_bits (v : Position (b+l))
    (z : (state hD hd H w).network.Half (lanePositions (cursorCoordinateLabels b l) v)) (side : Bool) :
    List.ofFn (fieldBits (state hD hd H w) _ z true (realSlot hd side)) =
      List.ofFn (buffers hD hd v z (.incoming side)) := by
  let I := iso hD hd H w
  let e := incomingArc v side
  have he : I.site v = (state hD hd H w).network.dst (I.edge (.inl e)) :=
    (congrArg I.site (head_incomingArc v side).symm).trans (I.dst (.inl e))
  let val := z.2 (I.edge (.inl e)) he
  have h := real_payload hD hd e ((I.payload (.inl e)).symm val)
  rw [Equiv.apply_symm_apply] at h
  exact (incoming_congr z (incoming_edge hD hd v side) _ he).trans h

omit [NeZero (b+l)] in
/-- Every slot at either end is genuine precisely at ordinal zero or one. -/
theorem field_width (u : (state hD hd H w).network.Site) (dir : Bool) (j : Fin (2^a)) :
    (state hD hd H w).halfWidth u dir j = if j.val < 2 then ramPayloadWidth (b+l) H w else 0 := by
  rw [ramPayloadWidth_eq_sum]
  cases dir with
  | false => exact cursorSlotWidth hD hd (bits (b := b) (l := l) H w) u.1.1 u.1.2 u.2 j
  | true =>
    let old := (state hD hd H w).slots.actualTarget.symm ((u.1,j),u.2)
    exact cursorSlotWidth hD hd (bits (b := b) (l := l) H w) old.1.1.1 old.1.1.2 old.2 j


theorem realSlot_val (side : Bool) : (realSlot hd side).val = side.toNat := by cases side <;> rfl

private theorem two_fields {m width : ℕ} (hm : 2 ≤ m) :
    (∑ i : Fin m, if i.val < 2 then width else 0) = 2*width := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Fin.sum_univ_add]
  have htail (j : Fin n) : ¬ 2 + j.val ≤ 1 := by omega
  simp [Fin.val_castAdd, Fin.val_natAdd, htail, two_mul]

omit [NeZero (b+l)] in
theorem end_width (u : (state hD hd H w).network.Site) (dir : Bool) :
    (∑ j, (state hD hd H w).halfWidth u dir j) = 2 * ramPayloadWidth (b+l) H w := by
  simp_rw [field_width hD hd]
  exact two_fields (by omega)

omit [NeZero (b+l)] in
theorem real_width (u : (state hD hd H w).network.Site) (dir side : Bool) :
    (state hD hd H w).halfWidth u dir (realSlot hd side) = ramPayloadWidth (b+l) H w := by
  rw [field_width hD hd, realSlot_val, ite_eq_left (by cases side <;> decide)]

/-- Ordinals of the two outgoing and the two incoming private vectors. -/
def portNumber (dir side : Bool) : ℕ := (if dir then 2 else 0) + side.toNat

/-- Select the incoming half-wire when the direction bit is true and the outgoing half-wire
otherwise, at the given side. -/
def port (dir side : Bool) : LocalPort := if dir then .incoming side else .outgoing side

omit [NeZero (b+l)] in
theorem real_offset (u : (state hD hd H w).network.Site) (dir side : Bool) :
    offset (state hD hd H w) u dir (realSlot hd side) = portNumber dir side * ramPayloadWidth (b+l) H w := by
  let X := state hD hd H w
  let j := realSlot hd side
  let width := ramPayloadWidth (b+l) H w
  have hj : j.val < 2 := by rw [realSlot_val]; cases side <;> decide
  have pre : ((List.ofFn (X.halfWidth u dir)).take j.val).sum = side.toNat * width := by
    rw [← Fin.ofFn_take_eq_take_ofFn j.isLt.le, List.sum_ofFn]
    calc
      _ = ∑ _ : Fin j.val, width := Finset.sum_congr rfl fun i _ => by
        change X.halfWidth u dir (Fin.castLE _ i) = width
        rw [field_width hD hd]
        exact ite_eq_left (i.isLt.trans hj)
      _ = _ := by simp [j, realSlot_val]
  change (if dir then ∑ k, X.halfWidth u false k else 0) + _ = _
  rw [pre, end_width hD hd]
  cases dir <;> simp [portNumber, Nat.add_mul, width]

omit [NeZero (b+l)] in
theorem packed_length_four (u : (state hD hd H w).network.Site) (z : (state hD hd H w).network.Half u) :
    (packed (state hD hd H w) u z).length = 4 * ramPayloadWidth (b+l) H w := by
  rw [packed_length, Fintype.sum_bool, end_width hD hd, end_width hD hd]
  omega

private theorem ofFn_bit {m n : ℕ} (x : Fin m → Bool) (y : Fin n → Bool) (he : m = n)
    (hb : List.ofFn x = List.ofFn y) (i : Fin n) : x (Fin.cast he.symm i) = y i := by
  subst n
  exact congrFun (List.ofFn_inj.mp hb) i

/-- The word actually read at the port offset of the private node arena
is the validator's requested bit of the independently supplied half-wires. -/
theorem read_port {ww : ℕ} (A : Arena) (node : ℕ) (v : Position (b+l))
    (z : (state hD hd H w).network.Half (lanePositions (cursorCoordinateLabels b l) v))
    (mem : BurstRAM.Word ww → BurstRAM.Word ww) (fit : A.base node + 4 * ramPayloadWidth (b+l) H w ≤ 2^ww)
    (dir side : Bool) (i : Fin (ramPayloadWidth (b+l) H w)) :
    PrivateFields.storeBits (A.base node) (packed (state hD hd H w) _ z) mem
        ((A.base node + portNumber dir side * ramPayloadWidth (b+l) H w + i.val : ℕ) : BurstRAM.Word ww) =
      PrivateFields.bitValue ww (buffers hD hd v z (port dir side) i) := by
  let X := state hD hd H w
  let u := lanePositions (cursorCoordinateLabels b l) v
  let j := realSlot hd side
  have len := real_width (H := H) (w := w) hD hd u dir side
  have hb : List.ofFn (fieldBits X u z dir j) = List.ofFn (buffers hD hd v z (port dir side)) := by
    cases dir with
    | false => exact outgoing_bits hD hd v z side
    | true => exact incoming_bits hD hd v z side
  have word := stored_member X u A node z mem ((packed_length_four hD hd u z) ▸ fit)
    dir j (Fin.cast len.symm i)
  change PrivateFields.storeBits (A.base node) (packed X u z) mem
      ((A.base node + offset X u dir j + i.val : ℕ) : BurstRAM.Word ww) = _ at word
  have hoff : offset X u dir j = portNumber dir side * ramPayloadWidth (b+l) H w := real_offset hD hd u dir side
  erw [hoff] at word
  exact word.trans (congrArg _ (ofFn_bit _ _ len hb i))

end PairSimulation.LeafArguments

end VPVNP
end Computability
end OAI
