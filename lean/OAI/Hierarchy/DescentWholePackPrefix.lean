import OAI.Hierarchy.DescentWholePackHistoryRAM
import OAI.Hierarchy.DescentMatchedPairOrdinal

namespace OAI
/-! # Reading the consumed capacity of every bin just before each physical first-fit decision -/

namespace Hierarchy.DescentPacking
open scoped Classical BigOperators
noncomputable section
variable {I V : Type*} [Fintype V] [DecidableEq V]

theorem pack_append (amount : I→ℕ) (xs ys : List I) (cap : V→ℕ) :
    (pack amount (xs++ys) cap).decisions=(pack amount xs cap).decisions++
      (pack amount ys (pack amount xs cap).remaining).decisions := by
  induction xs generalizing cap with
  | nil => rfl
  | cons x xs ih =>
    rw [pack_remaining_cons amount x xs cap]
    simp only [List.cons_append,pack_decisions_cons,ih]

theorem pack_take (amount : I→ℕ) (xs : List I) (cap : V→ℕ) (j : ℕ) :
    (pack amount (xs.take j) cap).decisions=(pack amount xs cap).decisions.take j := by
  induction xs generalizing cap j with
  | nil => cases j <;> rfl
  | cons x xs ih =>
    cases j with
    | zero => rfl
    | succ j => simp only [List.take_succ_cons,pack_decisions_cons,ih]

omit [Fintype V] in
theorem assigned_take (amount : I→ℕ) (v : V) (xs : List (I×Option V)) (j : ℕ) :
    assigned amount v (xs.take j) =
    ∑i : Fin xs.length,if i.val < j ∧ (xs.get i).2=some v then amount (xs.get i).1 else 0 := by
  induction xs generalizing j with
  | nil => simp [assigned]
  | cons p xs ih =>
    rcases p with ⟨a,sel⟩
    cases j with
    | zero => simp [assigned]
    | succ j =>
      let term (i : Fin (xs.length+1)) :=
        if i.val < j+1 ∧ (((a,sel)::xs).get i).2 = some v then amount (((a,sel)::xs).get i).1 else 0
      refine Eq.trans ?_ (Fin.sum_univ_succ term).symm
      simp only [term,List.take_succ_cons,assigned,List.get_cons_zero,List.get_cons_succ',
        Fin.val_zero,Fin.val_succ,Nat.zero_lt_succ,true_and,Nat.succ_lt_succ_iff,ih]

theorem used_prefix (amount : I→ℕ) (items : List I) (cap : V→ℕ) (j : ℕ) (v : V) :
    cap v-(pack amount (items.take j) cap).remaining v =
      ∑i : Fin (pack amount items cap).decisions.length,if i.val < j ∧
        ((pack amount items cap).decisions.get i).2=some v then amount ((pack amount items cap).decisions.get i).1 else 0 := by
  have account := (pack amount (items.take j) cap).account v
  rw [pack_take,assigned_take] at account
  omega


namespace FirstFitRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {w : ℕ}

theorem history_split (bits n base : ℕ) (src : ℕ→ℕ) (m : Memory w) (t i j : ℕ) :
    history n bits base src t (i+j) m=history n bits base src (t+i) j (history n bits base src t i m) := by
  induction i generalizing m t with
  | zero => simp only [Nat.zero_add,Nat.add_zero,history]
  | succ i ih =>
    rw [Nat.succ_add]
    simp only [history]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (m:=_) (t:=t+1)

theorem history_capacity_frame (bits n base : ℕ) (src : ℕ→ℕ) (m : Memory w) (t j x : ℕ)
    (lo : x < choiceWord bits base t) : history n bits base src t j m x=m x := by
  cases j with
  | zero => rfl
  | succ j =>
    have low : x<capacityBase bits base (t+1) := by rw [capacity_next];omega
    exact (history_before n bits base src _ (t+1) j x low).trans (frame _ _ _ _ _ _ m x lo low)

/-- The full physical sweep retains the actual prefix residual, even after later
units reuse the same bin. This amount determines its next old thick endpoint. -/
theorem remaining_read (bits base : ℕ) (src : ℕ→ℕ) (amount : I→ℕ) (items : List I)
    (cap : V→ℕ) (m : Memory w) (table : Fintype.card V≤2^bits) (early : ∀i,src i<base)
    (end_ : capacityBase bits base items.length+Fintype.card V<2^w)
    (start : capacityWords base cap m) (bounded : ∀v,cap v<2^w)
    (amounts : ∀i : Fin items.length,m (src i.val)=(amount (items.get i):Word w))
    (widths : ∀i∈items,amount i < 2^w)
    (j : ℕ) (live : j ≤ items.length) (v : V) :
    history (Fintype.card V) bits base src 0 items.length m
        (capacityBase bits base j+(Fintype.equivFin V v).val)=((pack amount (items.take j) cap).remaining v:Word w) := by
  let part := items.take j
  have len : part.length=j := by simp [part,live]
  have incl := Nat.mul_le_mul_right (2^bits+1) live
  have run := history_pack bits base 0 src amount part cap m table early
    (by simp only [Nat.zero_add,len];dsimp [capacityBase] at *;omega)
    (by simpa [capacityBase] using start) bounded
    (fun i=>by
      have lt : i.val < items.length := by have := i.isLt;omega
      simpa [part,List.get_eq_getElem] using amounts ⟨i.val,lt⟩)
    (fun i hi=>widths _ (List.take_subset j items hi))
  have row := run.1 v
  simp only [Nat.zero_add,len] at row
  rw [show items.length=j+(items.length-j) by omega,history_split,Nat.zero_add]
  apply Eq.trans (history_capacity_frame _ _ _ _ _ _ _ _ ?_) row
  have lt := (Fintype.equivFin V v).isLt.trans_le table
  dsimp [choiceWord]
  omega


end FirstFitRAM
end
end Hierarchy.DescentPacking

end OAI
