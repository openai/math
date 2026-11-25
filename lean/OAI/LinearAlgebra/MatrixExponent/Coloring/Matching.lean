import OAI.LinearAlgebra.MatrixExponent.Coloring.Shift
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# A perfect matching at arbitrary positive degree

Enlarge the edge array by one bit. Its second half contains a fixed
dummy matching of the supported vertices. Give each real and dummy
edge the quotient and remainder, respectively, when a power of two
is divided by the degree. Repeated halving deletes every dummy edge.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring

variable {h k : ℕ}

def degree (f : Fin (2 ^ h) → Fin (2 ^ k)) (x : Fin (2 ^ h) → Bool) (j : Fin (2 ^ k)) :=
  (Finset.univ.filter fun i => x i = true ∧ f i = j).card

def Regular (S : Finset (Fin (2 ^ k))) (d : ℕ) (L R : Fin (2 ^ h) → Fin (2 ^ k))
    (x : Fin (2 ^ h) → Bool) : Prop :=
  (∀ j, degree L x j = if j ∈ S then d else 0) ∧
  (∀ j, degree R x j = if j ∈ S then d else 0)

def halves (h : ℕ) : Fin (2 ^ h) ⊕ Fin (2 ^ h) ≃ Fin (2 ^ (h + 1)) :=
  finSumFinEquiv.trans (finCongr (by rw [pow_succ, mul_two]))

def join {α : Type} (f g : Fin (2 ^ h) → α) := Sum.elim f g ∘ (halves h).symm

def dummyLabel (S : Finset (Fin (2 ^ k))) (i : Fin (2 ^ h)) : Fin (2 ^ k) :=
  if ha : i.val < S.card then (S.equivFin.symm ⟨i.val, ha⟩).val else 0

def dummy (h : ℕ) : Fin (2 ^ (h + 1)) → Bool := join (fun _ => false) (fun _ => true)

def weights (S : Finset (Fin (2 ^ k))) (d : ℕ) (x : Fin (2 ^ h) → Bool) :=
  join (fun i => if x i then 2 ^ (h + 1) / d else 0)
    (fun i => if i.val < S.card then 2 ^ (h + 1) % d else 0)

def matching (S : Finset (Fin (2 ^ k))) (d : ℕ) (L R : Fin (2 ^ h) → Fin (2 ^ k))
    (x : Fin (2 ^ h) → Bool) (i : Fin (2 ^ h)) : Bool :=
  let y := (halve (join L (dummyLabel S)) (join R (dummyLabel S)) (dummy h))^[h + 1]
    (weights S d x)
  decide (y (halves h (.inl i)) = 1)

private theorem sum_halves (m : Fin (2 ^ (h + 1)) → ℕ) :
    ∑ i, m i = ∑ i, m (halves h (.inl i)) + ∑ i, m (halves h (.inr i)) := by
  rw [← (halves h).sum_comp, Fintype.sum_sum_type]

private theorem stock_join (f g : Fin (2 ^ h) → Fin (2 ^ k)) (m : Fin (2 ^ (h + 1)) → ℕ)
    (j : Fin (2 ^ k)) :
    stock (join f g) m j = stock f (fun i => m (halves h (.inl i))) j +
      stock g (fun i => m (halves h (.inr i))) j := by
  simp only [stock, Finset.sum_filter]
  rw [sum_halves]
  simp only [join, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]

private theorem stock_uniform (f : Fin (2 ^ h) → Fin (2 ^ k)) (x : Fin (2 ^ h) → Bool)
    (a : ℕ) (j : Fin (2 ^ k)) :
    stock f (fun i => if x i then a else 0) j = degree f x j * a := by
  unfold stock degree
  rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_filter]
  simp only [and_comm, nsmul_eq_mul, Nat.cast_id]

private theorem dummy_degree (S : Finset (Fin (2 ^ k))) (hs : S.card ≤ 2 ^ h) (j : Fin (2 ^ k)) :
    degree (dummyLabel (h := h) S) (fun i => decide (i.val < S.card)) j =
      if j ∈ S then 1 else 0 := by
  let P := Finset.univ.filter (fun i : Fin (2 ^ h) => i.val < S.card ∧ dummyLabel S i = j)
  suffices P.card = if j ∈ S then 1 else 0 by simpa [P, degree] using this
  by_cases hj : j ∈ S
  · let i := (S.equivFin ⟨j, hj⟩).castLE hs
    have h : P = {i} := by
      ext t
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨ht, he⟩
        rw [dummyLabel, dite_eq_left ht] at he
        have hh : S.equivFin.symm ⟨t.val, ht⟩ = ⟨j, hj⟩ := Subtype.ext he
        exact Fin.ext (congrArg (fun t : Fin S.card => t.val) (S.equivFin.symm_apply_eq.mp hh))
      · rintro rfl
        simp [dummyLabel, i]
    simp [h, hj]
  · have h : P = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨ht, he⟩ := (Finset.mem_filter.mp hi).2
      rw [dummyLabel, dite_eq_left ht] at he
      exact hj (he ▸ (S.equivFin.symm ⟨i.val, ht⟩).property)
    simp [h, hj]

variable {S : Finset (Fin (2 ^ k))} {d : ℕ} {L R : Fin (2 ^ h) → Fin (2 ^ k)} {x : Fin (2 ^ h) → Bool}

private theorem regular_stock (hs : S.card ≤ 2 ^ h)
    (he : ∀ j, degree L x j = if j ∈ S then d else 0) (j : Fin (2 ^ k)) :
    stock (join L (dummyLabel S)) (weights S d x) j = if j ∈ S then 2 ^ (h + 1) else 0 := by
  rw [stock_join]
  simp only [weights, join, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  have hg := stock_uniform (dummyLabel (h := h) S) (fun i => decide (i.val < S.card))
    (2 ^ (h + 1) % d) j
  simp only [decide_eq_true_eq, dummy_degree S hs] at hg
  rw [stock_uniform, he, hg]
  by_cases hj : j ∈ S
  · simp only [hj, ite_true, one_mul, Nat.div_add_mod]
  · simp [hj]

private theorem few_dummies (hd : 1 ≤ d) (hs : S.card * d ≤ 2 ^ h) :
    dummyStock (dummy h) (weights S d x) < 2 ^ (h + 1) := by
  rw [dummyStock, Finset.sum_filter, sum_halves]
  simp only [dummy, weights, join, Function.comp_apply, Equiv.symm_apply_apply,
    Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, ite_false, ite_true, Finset.sum_const_zero, zero_add]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  have hb : (Finset.univ.filter fun i : Fin (2 ^ h) => i.val < S.card).card ≤ S.card := by
    refine le_trans (Finset.card_le_card_of_injOn (t := Finset.range S.card)
      Fin.val ?_ Fin.val_injective.injOn) (Finset.card_range _).le
    exact fun _ hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  exact ((Nat.mul_le_mul hb (Nat.mod_lt _ hd).le).trans hs).trans_lt
    (by rw [pow_succ]; have := Nat.two_pow_pos h; omega)

theorem Regular.matching (he : Regular S d L R x) (hd : 1 ≤ d) (hs : S.card * d ≤ 2 ^ h) :
    Regular S 1 L R (matching S d L R x) ∧ ∀ i, matching S d L R x i = true → x i = true := by
  have sz := (Nat.le_mul_of_pos_right _ hd).trans hs
  let y := (halve (join L (dummyLabel S)) (join R (dummyLabel S)) (dummy h))^[h + 1] (weights S d x)
  obtain ⟨hl, hr, hm, hz⟩ := perfect S (regular_stock sz he.1) (regular_stock sz he.2) (few_dummies hd hs)
  have hz' (i : Fin (2 ^ h)) : y (halves h (.inr i)) = 0 := hz _ (by simp [dummy, join])
  let Y := MatrixExponent.Coloring.matching S d L R x
  have hy (i) : Y i = true ↔ y (halves h (.inl i)) = 1 := decide_eq_true_iff
  have aux (p : Fin (2 ^ h) → Fin (2 ^ k))
      (hp : ∀ j, stock (join p (dummyLabel S)) y j = if j ∈ S then 1 else 0) (j : Fin (2 ^ k)) :
      degree p Y j = if j ∈ S then 1 else 0 := by
    let m (i) := y (halves h (.inl i))
    have hv (k) : stock p m k = if k ∈ S then 1 else 0 := by
      rw [← hp, stock_join]
      simp [stock, hz', m]
    have hunit : m = (fun i => if Y i then 1 else 0) := by
      funext i
      have hh : m i ≤ stock p m (p i) := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
      rw [hv] at hh
      simp only [hy]
      change m i = if m i = 1 then 1 else 0
      split_ifs at * <;> omega
    simpa [hunit, stock_uniform] using hv j
  refine ⟨⟨aux L hl, aux R hr⟩, fun i hi => ?_⟩
  have hc : y (halves h (.inl i)) ≤ weights S d x (halves h (.inl i)) := hm _
  rw [(hy i).mp hi] at hc
  by_contra e
  simp [weights, join, e] at hc

end OAI.LinearAlgebra.MatrixExponent.Coloring
