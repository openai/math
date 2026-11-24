import OAI.Computability.VPVNP.SlotDemandSlices
import OAI.Computability.VPVNP.DegreeRefreshKernel
import OAI.Computability.VPVNP.ShrinkPayload
import Mathlib.Data.Fin.Tuple.Take

/-!
# Interval records for the compressor

Appendix E scans the widths in each of two ordered concatenations, then
intersects their fields in absolute coordinates. The output records name a
source and a target field and give their respective offsets and common length.
These computations never enumerate the individual bits of a payload.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open Compression.PackingData

/-- Position and extent of one field in an ordered concatenation. -/
structure Field where
  /-- Ordinal of this field within its ordered concatenation. -/
  index : ℕ
  /-- First absolute bit position of the field in the concatenation. -/
  start : ℕ
  /-- Number of consecutive bit positions belonging to the field. -/
  width : ℕ
  deriving DecidableEq

/-- The prefix scan assigns absolute starts and consecutive field numbers. -/
def fieldsFrom (index start : ℕ) : List ℕ → List Field
  | [] => []
  | w :: ws => ⟨index, start, w⟩ :: fieldsFrom (index + 1) (start + w) ws

@[simp] theorem fieldsFrom_length (ws : List ℕ) (index start : ℕ) :
    (fieldsFrom index start ws).length = ws.length := by
  induction ws generalizing index start <;> simp [fieldsFrom, *]

/-- The field at a list position stores its width and the sum of all previous widths. -/
theorem fieldsFrom_get (ws : List ℕ) (index start i : ℕ) (hi : i < ws.length) :
    (fieldsFrom index start ws)[i]'(by simpa using hi) =
      ⟨index + i, start + (ws.take i).sum, ws[i]⟩ := by
  induction ws generalizing index start i with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero => simp [fieldsFrom]
    | succ i =>
      have h : i < ws.length := by simpa using hi
      simp [fieldsFrom, ih (index + 1) (start + w) i h, Nat.add_assoc, Nat.add_comm 1]

/-- All indices and interval endpoints stay inside the two running totals. -/
theorem fieldsFrom_bounds {ws : List ℕ} {index start : ℕ} {f : Field}
    (h : f ∈ fieldsFrom index start ws) :
    index ≤ f.index ∧ f.index < index + ws.length ∧
      start ≤ f.start ∧ f.start + f.width ≤ start + ws.sum := by
  induction ws generalizing index start with
  | nil => simp [fieldsFrom] at h
  | cons w ws ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := ih h
      simp only [List.length_cons, List.sum_cons]
      omega

/-- Test membership of an absolute bit position in the field's half-open interval. -/
def Field.contains (f : Field) (x : ℕ) : Bool :=
  decide (f.start ≤ x ∧ x < f.start + f.width)

private theorem count_fields (ws : List ℕ) (index start x : ℕ) :
    (fieldsFrom index start ws).countP (fun f => f.contains x) =
      if start ≤ x ∧ x < start + ws.sum then 1 else 0 := by
  induction ws generalizing index start with
  | nil => simp [fieldsFrom]
  | cons w ws ih =>
    simp only [fieldsFrom, List.countP_cons, List.sum_cons, ih]
    simp only [Field.contains, decide_eq_true_eq]
    by_cases h₁ : start ≤ x <;> by_cases h₂ : x < start + w <;>
      by_cases h₃ : x < start + w + ws.sum <;>
      simp [← Nat.add_assoc, Nat.le_of_not_gt, *] <;> omega

/-- Each entry retains the two field references along with the three words
describing the contiguous copy. -/
structure SliceRecord where
  /-- The field in the source concatenation from which the intersection is copied. -/
  source : Field
  /-- The field in the target concatenation that receives the intersection. -/
  target : Field
  /-- The source offset, target offset, and length of the overlapping bit interval. -/
  slice : CopySlice

/-- One comparison of field endpoints. Empty intersections generate no copy. -/
def intersectFields (pair : Field × Field) : Option SliceRecord :=
  let s := pair.1
  let t := pair.2
  let slice := copySlice s.start s.width t.start t.width
  if slice.length = 0 then none else some ⟨s, t, slice⟩

/-- Candidate field pairs in source-major order. -/
def candidates (old new : List ℕ) : List (Field × Field) :=
  fieldsFrom 0 0 old ×ˢ fieldsFrom 0 0 new

/-- Construct copy records by scanning the two lists of fields. -/
def copyRecords (old new : List ℕ) : List SliceRecord :=
  (candidates old new).filterMap intersectFields

/-- The number of pair tests is independent of all numerical widths. -/
@[simp] theorem candidates_length (old new : List ℕ) :
    (candidates old new).length = old.length * new.length := by simp [candidates, List.length_product]

/-- At most one fixed-size record per pair of fields. -/
theorem copyRecords_length_le (old new : List ℕ) :
    (copyRecords old new).length ≤ old.length * new.length :=
  (List.length_filterMap_le _ _).trans_eq (candidates_length old new)

private theorem mem_copyRecords {old new : List ℕ} {r : SliceRecord} (h : r ∈ copyRecords old new) :
    r.source ∈ fieldsFrom 0 0 old ∧ r.target ∈ fieldsFrom 0 0 new ∧
    r.slice = copySlice r.source.start r.source.width r.target.start r.target.width ∧
    0 < r.slice.length := by
  obtain ⟨⟨s,t⟩, hp, he⟩ := List.mem_filterMap.mp h
  obtain ⟨hs,ht⟩ := List.mem_product.mp hp
  simp only [intersectFields] at he
  split at he
  · simp at he
  · obtain rfl := Option.some.inj he
    exact ⟨hs,ht,rfl,Nat.pos_of_ne_zero (by assumption)⟩

/-- All emitted records fit inside both named fields, including their offsets. -/
theorem copyRecords_bounds {old new : List ℕ} {r : SliceRecord} (h : r ∈ copyRecords old new) :
    0 < r.slice.length ∧
      r.slice.sourceOffset + r.slice.length ≤ r.source.width ∧
      r.slice.targetOffset + r.slice.length ≤ r.target.width ∧
      r.source.start + r.slice.sourceOffset = r.target.start + r.slice.targetOffset := by
  obtain ⟨_, _, hs, hp⟩ := mem_copyRecords h
  rw [hs] at hp ⊢
  simp only [copySlice] at hp ⊢
  omega

/-- Does this stored slice copy the bit with absolute index `x`? -/
def SliceRecord.copies (r : SliceRecord) (x : ℕ) : Bool :=
  let a := r.source.start + r.slice.sourceOffset
  decide (a ≤ x ∧ x < a + r.slice.length)

private theorem intersectFields_copies (pair : Field × Field) (x : ℕ) :
    ((intersectFields pair).map (fun r => r.copies x)).getD false =
      (pair.1.contains x && pair.2.contains x) := by
  obtain ⟨s,t⟩ := pair
  apply Bool.eq_iff_iff.mpr
  by_cases h : min (s.start + s.width) (t.start + t.width) - max s.start t.start = 0 <;>
    simp [intersectFields, copySlice, SliceRecord.copies, Field.contains, h] <;> omega

private theorem product_count {α β : Type*} (ss : List α) (ts : List β)
    (p : α → Bool) (q : β → Bool) :
    (ss ×ˢ ts).countP (fun ab => p ab.1 && q ab.2) = ss.countP p * ts.countP q := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    cases he : p s <;> simp [he, Function.comp_def, ih, Nat.add_mul, Nat.add_comm]

/-- Exact coverage, counting *occurrences* of records. With equal total widths
every absolute bit is copied exactly once, including when some fields have width zero. -/
theorem copyRecords_count (old new : List ℕ) (x : ℕ) :
    (copyRecords old new).countP (fun r => r.copies x) =
      if x < old.sum ∧ x < new.sum then 1 else 0 := by
  simp only [copyRecords, candidates, List.countP_filterMap, intersectFields_copies]
  refine (product_count (fieldsFrom 0 0 old) (fieldsFrom 0 0 new)
    (fun f => f.contains x) (fun f => f.contains x)).trans ?_
  simp only [count_fields, Nat.zero_le, true_and, Nat.zero_add]
  split_ifs <;> omega

/-- A copied bit has one intra-slice index. Both relative addresses at this
index refer to that same absolute bit. -/
theorem copyRecords_index {old new : List ℕ} {r : SliceRecord} (hr : r ∈ copyRecords old new)
    (x : ℕ) :
    r.copies x ↔ ∃! k : Fin r.slice.length,
      r.source.start + (r.slice.sourceOffset + k.val) = x ∧
      r.target.start + (r.slice.targetOffset + k.val) = x := by
  have hs := (copyRecords_bounds hr).2.2.2
  simp only [SliceRecord.copies, decide_eq_true_eq]
  constructor
  · rintro ⟨hl,hu⟩
    refine ⟨⟨x - (r.source.start + r.slice.sourceOffset), by omega⟩, ⟨by dsimp; omega, by dsimp; omega⟩, ?_⟩
    rintro k ⟨h,_⟩
    exact Fin.ext (by simp only; omega)
  · rintro ⟨k,⟨h,_⟩,_⟩
    have := k.isLt
    omega

private theorem field_unique {ws : List ℕ} {index start x : ℕ} {a b : Field}
    (ha : a ∈ fieldsFrom index start ws) (hb : b ∈ fieldsFrom index start ws)
    (hax : a.start ≤ x ∧ x < a.start + a.width) (hbx : b.start ≤ x ∧ x < b.start + b.width) :
    a = b := by
  induction ws generalizing index start with
  | nil => simp [fieldsFrom] at ha
  | cons w ws ih =>
    rcases List.mem_cons.mp ha with rfl | ha <;> rcases List.mem_cons.mp hb with rfl | hb
    · rfl
    · have := (fieldsFrom_bounds hb).2.2.1
      dsimp only at hax
      omega
    · have := (fieldsFrom_bounds ha).2.2.1
      dsimp only at hbx
      omega
    · exact ih ha hb

/-- Use a computed slice to read one bit, given access to old fields by number
and relative index. Only the selected old bit is requested. -/
def readCopiedBit (records : List SliceRecord) (oldBit : ℕ → ℕ → Bool) (x : ℕ) : Option Bool :=
  (records.find? fun r => r.copies x).map fun r =>
    let k := x - (r.source.start + r.slice.sourceOffset)
    oldBit r.source.index (r.slice.sourceOffset + k)

/-- The executable reader returns the old bit at the matching absolute
position in any repartition of the same total width. -/
theorem readCopiedBit_eq {old new : List ℕ} (htotal : old.sum = new.sum) {s : Field}
    (hs : s ∈ fieldsFrom 0 0 old) (i : Fin s.width) (bits : ℕ → ℕ → Bool) :
    readCopiedBit (copyRecords old new) bits (s.start + i.val) = some (bits s.index i.val) := by
  let x := s.start + i.val
  have hbound := (fieldsFrom_bounds hs).2.2.2
  have hi := i.isLt
  have hx : x < old.sum ∧ x < new.sum := by dsimp [x]; omega
  have hcount := copyRecords_count old new x
  rw [ite_eq_left hx] at hcount
  cases he : (copyRecords old new).find? fun r => r.copies x with
  | none =>
    have hn := List.countP_eq_zero.mpr (List.find?_eq_none.mp he)
    omega
  | some r =>
    have hr := List.mem_of_find?_eq_some he
    obtain ⟨rs,_,_,_⟩ := mem_copyRecords hr
    have ho := (copyRecords_bounds hr).2.1
    have hrc := List.find?_some he
    simp only [SliceRecord.copies, decide_eq_true_eq] at hrc
    have hrx : r.source.start ≤ x ∧ x < r.source.start + r.source.width := by omega
    have hsame : r.source = s :=
      field_unique rs hs hrx (by dsimp [x]; omega)
    change ((copyRecords old new).find? fun r => r.copies x).map _ = _
    rw [he]
    simp only [Option.map_some, Option.some.injEq, hsame]
    congr 1
    rw [hsame] at hrc
    dsimp only [x] at *
    omega

/-- The list scan agrees with the abstract concatenation offset in the shrinking kernel. -/
theorem orderedField_mem {A : Type*} {n : ℕ} (order : A ≃ Fin n) (w : A → ℕ) (a : A) :
    (⟨(order a).val, fieldStart order w a, w a⟩ : Field) ∈
      fieldsFrom 0 0 (List.ofFn fun i => w (order.symm i)) := by
  let ws := List.ofFn fun i => w (order.symm i)
  have hi : (order a).val < ws.length := by simp [ws]
  have h := List.getElem_mem (l := fieldsFrom 0 0 ws) (n := (order a).val) (by simpa using hi)
  rw [fieldsFrom_get ws 0 0 _ hi] at h
  simpa [ws, fieldStart, ← Fin.ofFn_take_eq_take_ofFn (order a).isLt.le, List.sum_ofFn,
    Fin.take] using h

/-- Generate the stored slice for a pair of fields, whenever it has positive length. -/
theorem record_mem_of_overlap {old new : List ℕ} (s t : Field)
    (hs : s ∈ fieldsFrom 0 0 old) (ht : t ∈ fieldsFrom 0 0 new)
    (hp : 0 < (copySlice s.start s.width t.start t.width).length) :
    ⟨s, t, copySlice s.start s.width t.start t.width⟩ ∈ copyRecords old new :=
  List.mem_filterMap.mpr ⟨(s,t), List.mem_product.mpr ⟨hs,ht⟩, by simp [intersectFields, hp.ne']⟩

/-- The widths supplied to the descriptor scan by a numbered bundle. -/
def orderedWidths {A : Type*} {n : ℕ} (order : A ≃ Fin n) (w : A → ℕ) : List ℕ :=
  List.ofFn fun i => w (order.symm i)

/-- Construct a field from its ordinal in the supplied order, the prefix width before it, and
its own width. -/
def numberedField {A : Type*} {n : ℕ} (order : A ≃ Fin n) (w : A → ℕ) (a : A) : Field :=
  ⟨(order a).val, fieldStart order w a, w a⟩

section Shrink

open Compression

variable {V H Tag L : Type} {d c : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable (number : P.BundleNumbering) (order : P.ThickNumbering) (w : Arc V H Tag L d c → ℕ)
variable (b : Site V Tag L × Fin d)

/-- Every bit read by the actual AB demand kernel has its slice in the output of the scan. -/
theorem demandBit_record (hc : 2 ≤ c) (hd : 0 < d) (a : P.ThickFiber b)
    (m : P.MotifFiber b) (i : Fin (w a.1.1)) (j : Fin (P.abWidth number w m.1))
    (h : P.demandBitEquiv hc hd number order w b ⟨m,j⟩ = ⟨a,i⟩) :
    let sw := fun s : P.ThickFiber b => w s.1.1
    let tw := fun t : P.MotifFiber b => P.abWidth number w t.1
    let r := (⟨numberedField (order b) sw a, numberedField (number b) tw m,
      P.demandSlice number order w b a m⟩ : SliceRecord)
    r ∈ copyRecords (orderedWidths (order b) sw) (orderedWidths (number b) tw) ∧
      ∃ k < r.slice.length, i.val = r.slice.sourceOffset + k ∧
        j.val = r.slice.targetOffset + k := by
  have he := (P.demandBitEquiv_eq_iff_slice number order w b hc hd a m i j).mp h
  obtain ⟨k,hk,hi,hj⟩ := he
  exact ⟨record_mem_of_overlap _ _ (orderedField_mem _ _ _) (orderedField_mem _ _ _)
    (Nat.zero_le k |>.trans_lt hk), k, hk, hi, hj⟩

end Shrink

open Compression Compression.ShrinkPayload in
/-- The same scan, with one surviving wire on its source side, reads the
subdivision bits used by both endpoint maps of the shrinking step. -/
theorem survivingSlice_read (b q : ℕ) (hq : 0 < q) (i : Fin q) (j : Fin (splitWidth b q i))
    (bits : ℕ → ℕ → Bool) :
    let t := numberedField (Equiv.refl (Fin q)) (splitWidth b q) i
    readCopiedBit (copyRecords [b] (List.ofFn (splitWidth b q))) bits (t.start + j.val) =
      some (sliceWords b q hq (fun k => bits 0 k.val) i j) := by
  let s : Field := ⟨0,0,b⟩
  have hs : s ∈ fieldsFrom 0 0 [b] := by simp [fieldsFrom, s]
  have htot : [b].sum = (List.ofFn (splitWidth b q)).sum := by simp [List.sum_ofFn, sum_splitWidth b q hq]
  have h := readCopiedBit_eq htot hs (sliceBits b q hq ⟨i,j⟩) bits
  change readCopiedBit _ bits _ = some (bits 0 (sliceBits b q hq ⟨i,j⟩).val)
  have hoff : (sliceBits b q hq ⟨i,j⟩).val =
      (numberedField (Equiv.refl (Fin q)) (splitWidth b q) i).start + j.val :=
    sliceBits_offset b q hq i j
  change readCopiedBit (copyRecords [b] (List.ofFn (splitWidth b q))) bits
    ((numberedField (Equiv.refl (Fin q)) (splitWidth b q) i).start + j.val) = _
  rw [← hoff]
  simpa only [s, Nat.zero_add] using h

section Refresh

open Compression.Refresh

/-- During a degree refresh the target list consists of one concatenated external word.
The generated descriptor for each nonempty source port gives precisely the offset at
which the local kernel reads its bit. -/
theorem refreshSegment_record {B : Type*} {d : ℕ} (w : Arc B d → ℕ) (s : B × Fin d)
    (j : Fin d) (i : Fin (w (s,j))) :
    let widths := fun k : Fin d => w (s,k)
    let source := numberedField (Equiv.refl (Fin d)) widths j
    let target := (⟨0, 0, ∑ k, widths k⟩ : Field)
    let r := (⟨source, target, copySlice source.start source.width target.start target.width⟩ :
      SliceRecord)
    r ∈ copyRecords (List.ofFn widths) [target.width] ∧
      r.slice.sourceOffset = 0 ∧ r.slice.length = w (s,j) ∧
      ∃ addr : Fin target.width, addr.val = r.slice.targetOffset + i.val ∧
        ∀ z : External w, segment w z (s,j) i = z s addr := by
  let source := numberedField (Equiv.refl (Fin d)) (fun k => w (s,k)) j
  let total := ∑ k : Fin d, w (s,k)
  have hwidth : 0 < w (s,j) := (Nat.zero_le i.val).trans_lt i.isLt
  let last : Fin (w (s,j)) := ⟨w (s,j) - 1, by omega⟩
  have hstart (k : Fin (w (s,j))) :
      (finSigmaFinEquiv (n := fun l => w (s,l)) ⟨j,k⟩).val = source.start + k.val :=
    segment_offset w s j k
  have hend := (finSigmaFinEquiv (n := fun k => w (s,k)) ⟨j,last⟩).isLt
  rw [hstart last] at hend
  change source.start + (w (s,j) - 1) < total at hend
  have hle : source.start + source.width ≤ total := by change source.start + w (s,j) ≤ total; omega
  have hs := orderedField_mem (Equiv.refl (Fin d)) (fun k => w (s,k)) j
  let target : Field := ⟨0,0,total⟩
  have ht : target ∈ fieldsFrom 0 0 [total] := by simp [target, fieldsFrom]
  have hlen : (copySlice source.start source.width 0 total).length = source.width := by
    simp [copySlice, min_eq_left hle]
  refine ⟨record_mem_of_overlap source target hs ht (hlen.symm ▸ hwidth), ?_, hlen, ?_⟩
  · simp [copySlice]
  · exact ⟨finSigmaFinEquiv (n := fun k => w (s,k)) ⟨j,i⟩, by simpa [copySlice] using hstart i,
      fun _ => rfl⟩

end Refresh

end CompressorRecords

end VPVNP
end Computability
end OAI
