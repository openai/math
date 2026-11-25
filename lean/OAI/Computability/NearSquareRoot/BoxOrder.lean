import OAI.Computability.NearSquareRoot.BoxRank
import OAI.Computability.NearSquareRoot.BoxFin
import Mathlib.Data.List.Forall2

/-! # The validity mask in tape order

The box directory lists the fastest axis first. The mask builder traverses the
axes in reverse, making a row of the faster axes for each valid digit and
inserting a row of zeros for each unused digit.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxOrder

/-- Local data in traversal order, with the slowest axis at the head.
The two entries are the numbers of valid and unused coordinates. -/
def shape (box : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (box.map fun p => (p.2, 2 ^ p.1 - p.2)).reverse

/-- A lexicographic scan accepts exactly the tuples whose every digit is valid. -/
def expand : List (ℕ × ℕ) → List Bool
  | [] => [true]
  | (a, b) :: xs =>
    let row := expand xs
    (List.replicate a row).flatten ++ List.replicate (b * row.length) false

def total (s : ℕ × ℕ) : ℕ := s.1 + s.2

@[simp] theorem length_expand (xs : List (ℕ × ℕ)) :
    (expand xs).length = (xs.map total).prod := by
  induction xs with
  | nil => simp [expand]
  | cons s xs ih =>
    rcases s with ⟨a,b⟩
    simp [expand, List.length_flatten, ih, total, add_mul]

@[simp] theorem count_expand (xs : List (ℕ × ℕ)) :
    (expand xs).count true = (xs.map Prod.fst).prod := by
  induction xs with
  | nil => simp [expand]
  | cons s xs ih => rcases s with ⟨a,b⟩; simp [expand, List.count_flatten, List.count_replicate, ih]

private theorem split_rows {a d : ℕ} (h : d < a) (row tail : List Bool) :
    ∃ rest, (List.replicate a row).flatten ++ tail =
      (List.replicate d row).flatten ++ (row ++ rest) := by
  refine ⟨(List.replicate (a-d-1) row).flatten ++ tail, ?_⟩
  conv_lhs => rw [show a = d + ((a-d-1)+1) by omega, List.replicate_add, List.replicate_succ]
  simp

private theorem in_row {pre row rest : List Bool} {i : ℕ} (hi : i < row.length) :
    (pre ++ (row ++ rest))[pre.length + i]? = row[i]? ∧
      ((pre ++ (row ++ rest)).take (pre.length + i)).count true =
        pre.count true + (row.take i).count true := by
  rw [List.getElem?_append_right (by omega : pre.length ≤ pre.length + i),
    Nat.add_sub_cancel_left, List.getElem?_append_left hi,
    List.take_length_add_append, List.take_append_of_le_length hi.le, List.count_append]
  exact ⟨rfl, rfl⟩

/-- The true occurrence at a valid padded address has the dense mixed-radix position. -/
theorem valid_position {ds : List ℕ} {xs : List (ℕ × ℕ)}
    (hd : List.Forall₂ (fun d p => d < p.1) ds xs) :
    let i := BoxRank.position (xs.map total) ds
    i < (expand xs).length ∧ (expand xs)[i]? = some true ∧
      ((expand xs).take i).count true = BoxRank.position (xs.map Prod.fst) ds := by
  induction hd with
  | nil => simp [expand, BoxRank.position]
  | @cons d ax ds xs hd _ ih =>
    obtain ⟨a, b⟩ := ax
    obtain ⟨hi, hget, hcount⟩ := ih
    let row := expand xs
    let i := BoxRank.position (xs.map total) ds
    let pre := (List.replicate d row).flatten
    have hip : i < row.length := hi
    have hp : pre.length = d * (xs.map total).prod := by simp [pre, row, List.length_flatten]
    have hc : pre.count true = d * (xs.map Prod.fst).prod := by
      simp [pre, row, List.count_flatten]
    obtain ⟨rest, heq⟩ := split_rows hd row (List.replicate (b * row.length) false)
    change expand ((a, b) :: xs) = pre ++ (row ++ rest) at heq
    have hin := in_row (pre := pre) (rest := rest) hip
    simp only [List.map_cons, BoxRank.position, heq, ← hp]
    refine ⟨by simp only [List.length_append]; omega, hin.1.trans hget, ?_⟩
    rw [hin.2, hc]
    exact congrArg (_ + ·) hcount

/-- On all padded tuples, the mask accepts exactly those in the product of
the cyclic orders. In particular a bad digit on any axis gives a zero row. -/
theorem padded_position {ds : List ℕ} {xs : List (ℕ × ℕ)}
    (hd : List.Forall₂ (fun d p => d < total p) ds xs) :
    let i := BoxRank.position (xs.map total) ds
    i < (expand xs).length ∧ ((expand xs)[i]? = some true ↔
      List.Forall₂ (fun d p => d < p.1) ds xs) := by
  induction hd with
  | nil => simp [expand, BoxRank.position]
  | @cons d ax ds xs hd _ ih =>
    obtain ⟨a,b⟩ := ax
    let row := expand xs
    let i := BoxRank.position (xs.map total) ds
    have hi : i < row.length := ih.1
    have hd' : d + 1 ≤ a + b := hd
    have hbound : d * row.length + i < (a+b) * row.length := calc
      _ < (d+1) * row.length := by rw [Nat.add_mul, Nat.one_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ hd'
    change d * (xs.map total).prod + i < (expand ((a,b) :: xs)).length ∧ _
    rw [length_expand, List.map_cons, List.prod_cons]
    refine ⟨by simpa only [row, length_expand, total] using hbound, ?_⟩
    change (expand ((a,b) :: xs))[d * (xs.map total).prod + i]? = some true ↔ _
    rw [List.forall₂_cons]
    change _ ↔ d < a ∧ _
    have hlen : (xs.map total).prod = row.length := (length_expand _).symm
    rw [hlen]
    by_cases hvalid : d < a
    · obtain ⟨rest, heq⟩ := split_rows hvalid row (List.replicate (b * row.length) false)
      change expand ((a,b) :: xs) = _ at heq
      have hp : (List.replicate d row).flatten.length = d * row.length := by
        simp [List.length_flatten]
      rw [heq, ← hp, (in_row hi).1, and_iff_right hvalid]
      exact ih.2
    · have hge : a * row.length ≤ d * row.length + i :=
        (Nat.mul_le_mul_right _ (Nat.le_of_not_gt hvalid)).trans (Nat.le_add_right ..)
      have he : (List.replicate a row).flatten.length = a * row.length := by
        simp [List.length_flatten]
      change ((List.replicate a row).flatten ++ List.replicate (b*row.length) false)[_]? = _ ↔ _
      rw [List.getElem?_append_right (he.trans_le hge), he, List.getElem?_replicate]
      rw [Nat.add_mul] at hbound
      simp [hvalid, show d * row.length + i - a * row.length < b * row.length by omega]

private theorem shape_total {k l : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid k l box) :
    (shape box).map total = (box.map (fun p => 2 ^ p.1)).reverse := by
  simp only [shape, List.map_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  exact Nat.add_sub_of_le (hb.axisBounds p hp).2.2.2

theorem length_shape {k l : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid k l box) :
    (expand (shape box)).length = 2 ^ k := by
  rw [length_expand, shape_total hb, List.prod_reverse, ← hb.widthSum]
  clear hb
  induction box with
  | nil => simp
  | cons p xs ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add]
    congr 1

theorem count_shape (box : List (ℕ × ℕ)) :
    (expand (shape box)).count true = (box.map Prod.snd).prod := by
  simp [shape, List.map_map, Function.comp_def]

private theorem aligned (box : List (ℕ × ℕ)) (t : Fin box.length → ℕ)
    (P : ℕ → (ℕ × ℕ) → Prop) :
    List.Forall₂ P (List.ofFn t).reverse (shape box) ↔
      ∀ i, P (t i) (BoxFin.modulus box i, BoxFin.padding box i) := by
  rw [shape, List.forall₂_reverse_iff, List.forall₂_map_right_iff, List.forall₂_iff_get]
  constructor
  · intro h i
    simpa [BoxFin.modulus, BoxFin.padding] using h.2 i.val (by simp) i.isLt
  · intro h
    refine ⟨by simp, fun i _ hi => ?_⟩
    simpa [BoxFin.modulus, BoxFin.padding] using h ⟨i, hi⟩

/-- An arbitrary binary address is marked if and only if all of its digits are
valid. This includes the unused space on every partially occupied axis. -/
theorem at_rank_iff {k l : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid k l box)
    (t : Fin box.length → ℕ) (ht : ∀ i, t i < 2 ^ (box.get i).1) :
    (expand (shape box))[CRT.rank (fun i => 2 ^ (box.get i).1) t]? = some true ↔
      ∀ i, t i < BoxFin.modulus box i := by
  have hp : List.Forall₂ (fun d p => d < total p) (List.ofFn t).reverse (shape box) := by
    apply (aligned ..).2
    intro i
    simpa only [total, BoxFin.modulus, BoxFin.padding,
      Nat.add_sub_of_le (hb.axisBounds _ (List.get_mem box i)).2.2.2] using ht i
  have h := (padded_position hp).2
  rw [shape_total hb, BoxRank.position_eq_rank, aligned] at h
  exact h

/-- At the padded address of any valid tuple, the number of true cells already
scanned is precisely the rank used by the scaled Chinese remainder permutation. -/
theorem at_rank {k l : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid k l box)
    (t : Fin box.length → ℕ) (ht : ∀ i, t i < BoxFin.modulus box i) :
    let p := CRT.rank (fun i => 2 ^ (box.get i).1) t
    (expand (shape box))[p]? = some true ∧
      ((expand (shape box)).take p).count true = CRT.rank (BoxFin.modulus box) t := by
  have hds : List.Forall₂ (fun d p => d < p.1) ((List.ofFn t).reverse) (shape box) :=
    (aligned ..).2 ht
  have h := (valid_position hds).2
  have ha : (shape box).map Prod.fst = (box.map Prod.snd).reverse := by
    simp [shape, List.map_map, Function.comp_def]
  rw [shape_total hb, ha, BoxRank.position_eq_rank, BoxRank.position_eq_rank] at h
  exact h

end BoxOrder

end NearSquareRoot
end Computability
end OAI
