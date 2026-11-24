import OAI.Computability.VPVNP.Hamiltonian
import OAI.Computability.VPVNP.QueryProgram
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Reading a directed Hamiltonian cycle row by row

A running control stores the number of completed rows, the current vertex, the column
to inspect, and the unique edge found so far in the row. Each transition reads one
payload bit. A second edge in a row or an empty row immediately gives a rejection.
-/

namespace OAI
namespace Computability
namespace VPVNP

/-- A halted result or a row count, vertex, column, and previously found successor. -/
abbrev CycleState (m : ℕ) := Bool ⊕ (Fin m × Fin m × Fin m × Option (Fin m))

/-- Continue the traversal at the unique edge's target. The first return must occur
after exactly `m` rows. -/
def afterRow {m : ℕ} (root t w : Fin m) : CycleState m :=
  if h : t.val + 1 < m then
    if w = root then .inl false else .inr (⟨t.val + 1, h⟩, w, ⟨0, root.pos⟩, none)
  else .inl (w == root)

private def readEdge {m : ℕ} (root t v j : Fin m) (acc : Option (Fin m)) (bit : Bool) :
    CycleState m :=
  if bit = true ∧ acc ≠ none then .inl false else
    let found := if bit then some j else acc
    if h : j.val + 1 < m then .inr (t, v, ⟨j.val + 1, h⟩, found)
    else match found with
      | some w => afterRow root t w
      | none => .inl false

/-- A fixed finite control for an `m × m` binary adjacency matrix in row-major order. -/
def cycleQuery {m : ℕ} (root : Fin m) : QueryProgram (m * m) (CycleState m) where
  start := .inr (⟨0, root.pos⟩, root, ⟨0, root.pos⟩, none)
  step
    | .inl b => .halt b
    | .inr (t, v, j, acc) =>
      .read (finProdFinEquiv (v, j)) (readEdge root t v j acc false) (readEdge root t v j acc true)

@[simp] theorem cycleQuery_eval_halt {m : ℕ} (root : Fin m) (bits : Fin (m * m) → Bool)
    (fuel : ℕ) (b : Bool) : (cycleQuery root).eval bits fuel (.inl b) = b := by
  cases fuel <;> rfl

private theorem cycleQuery_eval_read {m : ℕ} (root : Fin m) (x : Fin m × Fin m → Bool)
    (fuel : ℕ) (t v j : Fin m) (acc : Option (Fin m)) :
    (cycleQuery root).eval (x ∘ finProdFinEquiv.symm) (fuel + 1) (.inr (t, v, j, acc)) =
      (cycleQuery root).eval (x ∘ finProdFinEquiv.symm) fuel (readEdge root t v j acc (x (v, j))) := by
  simp only [QueryProgram.eval, cycleQuery, Function.comp_apply, Equiv.symm_apply_apply]
  cases h : x (v, j) <;> rfl

private theorem rowSuccessor_eq_of_single {m : ℕ} (x : Fin m × Fin m → Bool) (v w : Fin m)
    (h : ∀ k, x (v, k) = true ↔ w = k) : rowSuccessor x v = w := by
  unfold rowSuccessor
  cases hfind : (List.finRange m).find? (fun k => x (v, k)) with
  | none =>
    have hmiss := List.find?_eq_none.mp hfind w (List.mem_finRange _)
    simp [(h w).2 rfl] at hmiss
  | some k =>
    have hk := List.find?_some hfind
    exact ((h k).1 hk).symm

private theorem row_eq_decide_of_single {m : ℕ} (x : Fin m × Fin m → Bool) (v w : Fin m)
    (h : ∀ k, x (v, k) = true ↔ w = k) : ∀ k, x (v, k) = decide (rowSuccessor x v = k) := by
  intro k
  rw [rowSuccessor_eq_of_single x v w h]
  exact Bool.eq_iff_iff.mpr (by simpa using h k)

private def RowPrefix {m : ℕ} (b : Fin m → Bool) (n : ℕ) (a : Option (Fin m)) : Prop :=
  (∀ k : Fin m, k.val < n → (b k = true ↔ a = some k)) ∧
    (∀ k : Fin m, a = some k → k.val < n)

private theorem rowPrefix_zero {m : ℕ} (b : Fin m → Bool) : RowPrefix b 0 none := by
  simp [RowPrefix]

private theorem rowPrefix_step {m : ℕ} {b : Fin m → Bool} (j : Fin m) {a : Option (Fin m)}
    (ha : RowPrefix b j.val a) (hok : b j = true → a = none) :
    RowPrefix b (j.val + 1) (if b j then some j else a) := by
  obtain ⟨hbits, hbound⟩ := ha
  cases h : b j with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    refine ⟨fun k hk => ?_, fun k hak => Nat.lt_succ_of_lt (hbound k hak)⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
    · exact hbits k hk
    · have heq : k = j := Fin.ext hk
      subst k
      have hne : a ≠ some j := fun hj => Nat.lt_irrefl _ (hbound j hj)
      simp [h, hne]
  | true =>
    have ha := hok h
    subst a
    simp only [ite_true]
    constructor
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · have hne : j ≠ k := by
          rintro rfl
          exact Nat.lt_irrefl _ hk
        simpa [hne] using hbits k hk
      · have heq : k = j := Fin.ext hk
        subst k
        simp [h]
    · rintro k hk
      obtain rfl := Option.some.inj hk
      exact Nat.lt_succ_self _

private theorem scanRow {m : ℕ} (root : Fin m) (x : Fin m × Fin m → Bool)
    (f : ℕ) (t v j : Fin m) (acc : Option (Fin m))
    (ha : RowPrefix (fun k => x (v, k)) j.val acc) :
    (cycleQuery root).eval (x ∘ finProdFinEquiv.symm) (f + (m - j.val))
      (.inr (t, v, j, acc)) =
      if (∀ k, x (v, k) = decide (rowSuccessor x v = k)) then
        (cycleQuery root).eval (x ∘ finProdFinEquiv.symm) f (afterRow root t (rowSuccessor x v))
      else false := by
  have htime : f + (m - j.val) = (f + (m - (j.val + 1))) + 1 := by omega
  rw [htime, cycleQuery_eval_read]
  by_cases hbad : x (v, j) = true ∧ acc ≠ none
  · obtain ⟨hb, hne⟩ := hbad
    cases acc with
    | none => exact False.elim (hne rfl)
    | some w =>
      have hw : w.val < j.val := ha.2 w rfl
      have hxw : x (v, w) = true := (ha.1 w hw).mpr rfl
      have invalid : ¬ ∀ k, x (v, k) = decide (rowSuccessor x v = k) := by
        intro valid
        have e₁ := (valid w).symm.trans hxw
        have e₂ := (valid j).symm.trans hb
        have eq := (of_decide_eq_true e₁).symm.trans (of_decide_eq_true e₂)
        exact (ne_of_lt hw) (congrArg Fin.val eq)
      simp [readEdge, hb, invalid]
  · have hok : x (v, j) = true → acc = none := by
      intro hj
      by_contra h
      exact hbad ⟨hj, h⟩
    have hn := rowPrefix_step j ha hok
    simp only [readEdge, ite_eq_right hbad]
    by_cases hnext : j.val + 1 < m
    · rw [dite_eq_left hnext]
      exact scanRow root x f t v ⟨j.val + 1, hnext⟩ _ hn
    · rw [dite_eq_right hnext]
      have hdone : m - (j.val + 1) = 0 := by omega
      simp only [hdone, Nat.add_zero]
      generalize hfound : (if x (v, j) then some j else acc) = found at hn ⊢
      cases found with
      | none =>
        have invalid : ¬ ∀ k, x (v, k) = decide (rowSuccessor x v = k) := by
          intro valid
          let k := rowSuccessor x v
          have hxk : x (v, k) = true := by simpa [k] using valid k
          have hkm := k.isLt
          have := (hn.1 k (by omega)).mp hxk
          contradiction
        simp [invalid]
      | some w =>
        have single (k : Fin m) : x (v, k) = true ↔ w = k := by
          have hkm := k.isLt
          simpa using hn.1 k (by omega)
        have hw : rowSuccessor x v = w := rowSuccessor_eq_of_single x v w single
        have valid := row_eq_decide_of_single x v w single
        simp [valid, hw]
termination_by m - j.val

/-- With the remaining clock increased by one row, the scan either rejects the row or
continues with its unique successor and exactly the original remaining clock. -/
theorem cycleQuery_eval_row {m : ℕ} (root : Fin m) (x : Fin m × Fin m → Bool)
    (f : ℕ) (t v : Fin m) :
    (cycleQuery root).eval (x ∘ finProdFinEquiv.symm) (f + m) (.inr (t, v, ⟨0, v.pos⟩, none)) =
      if (∀ k, x (v, k) = decide (rowSuccessor x v = k)) then
        (cycleQuery root).eval (x ∘ finProdFinEquiv.symm) f (afterRow root t (rowSuccessor x v))
      else false := by
  exact scanRow root x f t v ⟨0, v.pos⟩ none (rowPrefix_zero _)

end VPVNP
end Computability
end OAI
