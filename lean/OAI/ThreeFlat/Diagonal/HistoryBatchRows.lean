import OAI.ThreeFlat.Diagonal.HistoryPostorder

namespace OAI
/-! # Closed address formulas for the two homogeneous runs in each motif batch -/

namespace ThreeFlat.Diagonal.HistoryContraction.Tree.BatchRows

open scoped BigOperators

/-- Prefix for a stream with `r` entries of size `a` followed by entries of size `b`. -/
def span (r a b i : ℕ) := min i r*a+(i-r)*b

theorem span_range (r a b i : ℕ) : (∑ x ∈ Finset.range i, if x<r then a else b) = span r a b i := by
  induction i with
  | zero => simp [span]
  | succ i ih =>
    rw [Finset.sum_range_succ,ih]
    by_cases h : i<r
    · simp [span,h,Nat.min_eq_left h.le,Nat.sub_eq_zero_of_le h.le,
        Nat.sub_eq_zero_of_le h,Nat.succ_mul]
    · have h' : r≤ i := by omega
      have add : i+1-r=(i-r)+1 := by omega
      simp [span,h,Nat.min_eq_right h',Nat.min_eq_right (Nat.le_succ_of_le h'),add,Nat.succ_mul,Nat.add_assoc]

variable {F : Type*} {r s h p : ℕ}

private theorem span_fin (a b i : ℕ) : (∑ x : Fin i, if x.val<r then a else b) = span r a b i := by
  calc
    _ = ∑ x ∈ Finset.range i, if x<r then a else b := by rw [←Fin.sum_univ_eq_sum_range]
    _ = _ := span_range r a b i

private theorem prefix_value {t : Fin (r+s) → ℕ} (a b : ℕ) (val : ∀ i, t i = if i.val<r then a else b)
    (j : Fin (r+s)) : before t j = span r a b j.val := by
  simp only [before,val,Fin.val_castLE,span_fin]

private theorem full_value {t : Fin (r+s) → ℕ} (a b : ℕ) (val : ∀ i, t i = if i.val<r then a else b) :
    (∑ i,t i) = r*a+s*b := by
  simp only [val,span_fin,span,Nat.min_eq_right (Nat.le_add_right r s),Nat.add_sub_cancel_left]

structure Size where
  arity : ℕ
  rows : ℕ
  bits : ℕ

variable {arity : Fin (r+s) → ℕ} (N : (i : Fin (r+s)) → BitNetwork F (arity i))
    (wire : ∀ i, Fin (arity i) → BitSource h p) (L R : Size)

structure Sizes : Prop where
  arities : ∀ i, arity i = if i.val<r then L.arity else R.arity
  cells : ∀ i, (N i).cells = if i.val<r then L.rows else R.rows
  internal : ∀ i, (N i).internal = if i.val<r then L.bits else R.bits

def record (root : Addresses) (r s : ℕ) (L R : Size) (i : ℕ) : Copy :=
  let rows := span r L.rows R.rows i
  let bits := span r L.bits R.bits i
  let total := r*L.rows+s*R.rows
  ⟨root.nodes+4*i,root.nodes+4*(r+s),root.maps+span r L.arity R.arity i,
   rows,bits,root.tasks+5*i,root.stream+4*rows,root.stream+4*total+4*rows,
   4*(if i<r then L.rows else R.rows)⟩

private theorem prefix_blocks (b : Addresses) (j : Fin (r+s)) :
    childStart b (fun i => Tree.atom (N i)) j =
    ⟨b.stream+4*before (fun i => (N i).cells) j,b.maps,b.nodes+4*j.val,b.tasks⟩ := by
  simp [childStart,Addresses.after,Counts.prefix,footprint,before,Finset.mul_sum]

private theorem parent_fields (b : Addresses) :
    let T := Tree.join h (r+s) arity wire (fun i => Tree.atom (N i))
    rootNode b T = b.nodes+4*(r+s) ∧ rootStream b T=b.stream+4*(∑ i,(N i).cells) := by
  simp [rootNode,rootStream,within,Addresses.after,footprint,rows,Finset.mul_sum,Nat.mul_add]; omega

/-- Every task of a party admission or payload batch can be calculated from
one ordinal, two leaf sizes and the four starting addresses. -/
theorem record_at (sz : Sizes N L R) (b : Addresses) (j : Fin (r+s)) :
    copy b wire (fun i => Tree.atom (N i)) j = record b r s L R j.val := by
  have root := parent_fields N wire b
  simp only [copy,record,prefix_blocks,root.1,root.2,rows,bits]
  simp [rootNode,rootStream,within,Addresses.after,footprint,rows,
    prefix_value L.arity R.arity sz.arities,prefix_value L.rows R.rows sz.cells,
    prefix_value L.bits R.bits sz.internal,full_value L.rows R.rows sz.cells,sz.cells j,
    Nat.mul_add]

end ThreeFlat.Diagonal.HistoryContraction.Tree.BatchRows

end OAI
