import OAI.Hierarchy.TaggedSortedKeys
import OAI.Hierarchy.TaggedStableObservations
import Mathlib.Data.List.FinRange

namespace OAI
/-! # Stable observation and trimming of a global packed sort

A nonempty pack reads its digit from its first lane. Every live lane then has
the same key as the entire word. The stable sort preserves each digit bucket,
and its high dummy bit keeps all nonempty packs inside the retained prefix.
-/

noncomputable section
namespace Hierarchy.Tagged.WideOrder

open ThreeFlat Routing SortNetwork
open Radix SortedBlock
open scoped Classical

variable {u p w d : ℕ}

def lane (v : Bits (p*w)) (l : Fin p) : Bits w := fun j => v (finProdFinEquiv (l,j))

def head (hp : 0 < p) (j : Fin w) : Fin (p*w) := finProdFinEquiv (⟨0,hp⟩,j)

def order (hp : 0 < p) (digit : Fin d → Fin w) (dummy : Fin w) : Fin (d+1) → Fin (p*w) :=
  fun i => head hp (PassShape.maskedDigit digit dummy i)

def live (real : Fin w) (v : Bits (p*w)) : List (Bits w) :=
  (List.ofFn (lane v)).filter (fun r => r real)

def observed (real : Fin w) (X : Records u (p*w)) : List (Bits w) :=
  (List.ofFn (id : Row u → Row u)).flatMap (fun i => live real (X i))

def before (cap : ℕ) (real : Fin w) (X : Records u (p*w)) : List (Bits w) :=
  ((List.ofFn (id : Row u → Row u)).take cap).flatMap (fun i => live real (X i))

def Homogeneous (hp : 0 < p) (digit : Fin d → Fin w) (real : Fin w) (X : Records u (p*w)) : Prop :=
  ∀ i j, lane (X i) j real = true →
    lane (X i) ⟨0,hp⟩ real = true ∧
      readKey digit (lane (X i) j) = readKey digit (lane (X i) ⟨0,hp⟩)

private theorem order_eq (hp : 0 < p) (digit : Fin d → Fin w) (dummy : Fin w) :
    order hp digit dummy = PassShape.maskedDigit (fun i => head hp (digit i)) (head hp dummy) :=
  Fin.comp_snoc (head hp) digit dummy

private def packKey (hp : 0 < p) (digit : Fin d → Fin w) (dummy : Fin w)
    (X : Records u (p*w)) (i : Row u) : Row (d+1) :=
  addressEquiv (d+1) (X i ∘ order hp digit dummy)

private theorem key_of_mem (hp : 0 < p) (digit : Fin d → Fin w) (real dummy : Fin w)
    (X : Records u (p*w)) (same : Homogeneous hp digit real X)
    (flags : ∀ i j, lane (X i) j dummy = !(lane (X i) j real)) (i : Row u) {v : Bits w}
    (hv : v ∈ live real (X i)) : readKey digit v = (packKey hp digit dummy X i).val := by
  obtain ⟨mem,alive⟩ := List.mem_filter.mp hv
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp mem
  obtain ⟨first,eq⟩ := same i j alive
  change _ = readKey (PassShape.maskedDigit digit dummy) (lane (X i) ⟨0,hp⟩)
  simp only [masked_value, flags, first, Bool.not_true, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
  exact eq

/-- All surviving lane digits are ordered, including lanes in the same pack. -/
theorem sorted (hp : 0 < p) (digit : Fin d → Fin w) (real dummy : Fin w)
    (X : Records u (p*w)) (same : Homogeneous hp digit real X)
    (flags : ∀ i j, lane (X i) j dummy = !(lane (X i) j real)) :
    (observed real (stable (order hp digit dummy) X)).Pairwise
      (fun a b => readKey digit a ≤ readKey digit b) := by
  let key := packKey hp digit dummy X
  let e := Tuple.sort key
  change ((List.ofFn (id : Row u → Row u)).flatMap (fun i => live real (X (e i)))).Pairwise _
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    rw [key_of_mem hp digit real dummy X same flags (e i) ha,
      key_of_mem hp digit real dummy X same flags (e i) hb]
  · apply List.pairwise_ofFn.mpr
    intro i j lt a ha b hb
    rw [key_of_mem hp digit real dummy X same flags (e i) ha,
      key_of_mem hp digit real dummy X same flags (e j) hb]
    exact Tuple.monotone_sort key lt.le

private theorem sort_val {n m : ℕ} (key : Fin n → Fin m) :
    Tuple.sort (fun i => (key i).val) = Tuple.sort key := by
  symm
  obtain ⟨le,tie⟩ := Tuple.eq_sort_iff.mp (rfl : Tuple.sort key = _)
  exact Tuple.eq_sort_iff.mpr ⟨fun i j h => le h,fun i j h eq => tie i j h (Fin.ext eq)⟩

/-- Stable sorting whole words preserves the original list of lanes at each
digit, including repeated records and any number of inactive lanes. -/
theorem buckets (hp : 0 < p) (digit : Fin d → Fin w) (real dummy : Fin w)
    (X : Records u (p*w)) (same : Homogeneous hp digit real X)
    (flags : ∀ i j, lane (X i) j dummy = !(lane (X i) j real)) (a : ℕ) :
    bucket (readKey digit) a (observed real (stable (order hp digit dummy) X)) =
      bucket (readKey digit) a (observed real X) := by
  let key := packKey hp digit dummy X
  let e := Tuple.sort key
  let read (i : Row u) := bucket (readKey digit) a (live real (X i))
  have only (i : Row u) (ne : (key i).val ≠ a) : read i = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro v hv hit
    exact ne ((key_of_mem hp digit real dummy X same flags i hv).symm.trans (of_decide_eq_true hit))
  have order := stable_observe_packs (fun i => (key i).val) a read only
  rw [sort_val] at order
  change (List.ofFn e).flatMap read = _ at order
  have perm : List.ofFn e = (List.ofFn (id : Row u → Row u)).map e := List.ofFn_comp' id e
  rw [perm, List.flatMap_map] at order
  have actual : e = Tuple.sort
      (fun i => addressEquiv (d+1) (X i ∘ WideOrder.order hp digit dummy)) := rfl
  rw [actual] at order
  simpa only [bucket, observed, List.filter_flatMap, read, stable, Function.comp_apply]
    using order

/-- Upper physical pack slots have no live lane after sorting whenever the
input contained at most the retained prefix of potentially nonempty packs. -/
theorem sorted_support (hp : 0 < p) (digit : Fin d → Fin w) (real dummy : Fin w)
    (X : Records u (p*w)) (same : Homogeneous hp digit real X)
    (flags : ∀ i j, lane (X i) j dummy = !(lane (X i) j real)) {cap : ℕ}
    (support : ∀ i : Row u, lane (X i) ⟨0,hp⟩ real = true → i.val < cap) :
    ∀ i j, lane ((stable (order hp digit dummy) X) i) j real = true → i.val < cap := by
  let mask := PassShape.maskedDigit (fun i => head hp (digit i)) (head hp dummy)
  let e := Tuple.sort (fun i => addressEquiv (d+1) (X i ∘ mask))
  have flags' (i : Row u) : X i (head hp dummy) = !(X i (head hp real)) := flags i ⟨0,hp⟩
  have front := sort_prefix (fun i => head hp (digit i)) (head hp real) (head hp dummy) X flags'
  have bound := SortedBlock.bound mask (head hp real) X support
  intro i j alive
  rw [order_eq] at alive
  have first := (same (e i) j alive).1
  exact ((front i).mp first).trans_le bound

/-- Taking the prescribed number of output packs preserves the full live read. -/
theorem trim {cap : ℕ} (real : Fin w) (X : Records u (p*w))
    (support : ∀ i j, lane (X i) j real = true → i.val < cap) :
    before cap real X = observed real X := by
  let rows := List.ofFn (id : Row u → Row u)
  have nil : (rows.drop cap).flatMap (fun i => live real (X i)) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro i hi
    obtain ⟨j,room,eq⟩ := List.mem_drop_iff_getElem.mp hi
    have index : cap+j = i.val := by simpa [rows] using congrArg Fin.val eq
    apply List.filter_eq_nil_iff.mpr
    intro v hv alive
    obtain ⟨l,rfl⟩ := List.mem_ofFn.mp hv
    have bound := support i l alive
    omega
  change (rows.take cap).flatMap _ = rows.flatMap _
  conv_rhs => rw [← List.take_append_drop cap rows, List.flatMap_append, nil, List.append_nil]

end Hierarchy.Tagged.WideOrder

end
end OAI
