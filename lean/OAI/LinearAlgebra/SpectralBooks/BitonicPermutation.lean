import OAI.LinearAlgebra.SpectralBooks.BitonicNetwork
import Mathlib.Data.Fin.Tuple.Sort

namespace OAI
/-! # Comparator networks preserve the multiset of records

For each fixed input, compare-and-exchange selects a permutation of the input wires.
This also accounts for repeated keys and equal records.
-/

namespace LinearAlgebra.SpectralBooks.Batcher

/-- Exchange the two entries in each pair precisely when the left key is larger. -/
private def compareRoute {α I : Type*} [LinearOrder α] (l r : I → α) : Equiv.Perm (I ⊕ I) :=
  let route : I ⊕ I → I ⊕ I := Sum.elim
    (fun i ↦ if l i ≤ r i then Sum.inl i else Sum.inr i)
    (fun i ↦ if l i ≤ r i then Sum.inr i else Sum.inl i)
  have inv : Function.Involutive route := by
    intro j
    cases j with
    | inl i => by_cases h : l i ≤ r i <;> simp [route, h]
    | inr i => by_cases h : l i ≤ r i <;> simp [route, h]
  inv.toPerm

/-- There is a bijection matching each output position with an input position
carrying the same record. -/
theorem Network.exists_eval_eq_comp_perm {k : ℕ} {α : Type*} [LinearOrder α]
    (N : Network k) (x : Wires k α) :
    ∃ e : Equiv.Perm (Fin (2^k)), N.eval x = x ∘ e := by
  induction N with
  | nil => exact ⟨.refl _, rfl⟩
  | reverse => exact ⟨Fin.revPerm, rfl⟩
  | @compareHalves k =>
    refine ⟨(splitEquiv k).permCongr (compareRoute (x ∘ low) (x ∘ high)), ?_⟩
    funext j
    rcases low_or_high j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [Network.eval, join_low]
      by_cases h : x (splitEquiv k (.inl i)) ≤ x (splitEquiv k (.inr i))
      · simp [Equiv.permCongr_apply, compareRoute, Function.Involutive.toPerm, low, high, h]
      · simp [Equiv.permCongr_apply, compareRoute, Function.Involutive.toPerm, low, high, h,
          min_eq_right (le_of_not_ge h)]
    · rw [Network.eval, join_high]
      by_cases h : x (splitEquiv k (.inl i)) ≤ x (splitEquiv k (.inr i))
      · simp [Equiv.permCongr_apply, compareRoute, Function.Involutive.toPerm, low, high, h]
      · simp [Equiv.permCongr_apply, compareRoute, Function.Involutive.toPerm, low, high, h,
          max_eq_left (le_of_not_ge h)]
  | @parallel k l r ihl ihr =>
    obtain ⟨el, hl⟩ := ihl (x ∘ low)
    obtain ⟨er, hr⟩ := ihr (x ∘ high)
    refine ⟨(splitEquiv k).permCongr (el.sumCongr er), ?_⟩
    funext j
    rcases low_or_high j with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp [Network.eval, hl, hr, Equiv.permCongr_apply, low, high, join]
  | seq a b iha ihb =>
    obtain ⟨ea, ha⟩ := iha x
    obtain ⟨eb, hb⟩ := ihb (a.eval x)
    exact ⟨eb.trans ea, by rw [Network.eval, hb, ha]; rfl⟩

/-- In list form every value occurs with its original multiplicity. -/
theorem Network.perm_ofFn_eval {k : ℕ} {α : Type*} [LinearOrder α]
    (N : Network k) (x : Wires k α) : (List.ofFn (N.eval x)).Perm (List.ofFn x) := by
  obtain ⟨e, he⟩ := N.exists_eval_eq_comp_perm x
  rw [he]
  exact e.ofFn_comp_perm x

/-- A sorted comparator output is the canonical sorted tuple. -/
theorem Network.eval_eq_sort_iff {k : ℕ} {α : Type*} [LinearOrder α]
    (N : Network k) (x : Wires k α) :
    N.eval x = x ∘ Tuple.sort x ↔ Monotone (N.eval x) := by
  obtain ⟨e, he⟩ := N.exists_eval_eq_comp_perm x
  rw [he]
  exact Tuple.comp_sort_eq_comp_iff_monotone

end LinearAlgebra.SpectralBooks.Batcher

end OAI
