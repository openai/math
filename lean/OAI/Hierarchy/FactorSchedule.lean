import OAI.Hierarchy.FactorAllocation
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # The actual factors computed at a tick of the diagonal schedule -/

namespace Hierarchy.FactorAllocation

/-- Within a class, retain the original occurrence order at each tick. -/
def atTick {α : Type*} {T : ℕ} (xs : List α) (t : Fin T) : List α :=
  (List.ofFn (fun i : Fin xs.length =>
    if i.val ≡ t.val [MOD T] then [xs[i]] else [])).flatten

/-- Concatenate classes in the base representation of their bucket tuples. -/
def factors {α : Type*} {T d : ℕ} (w : ℕ) (cost : α → Fin d → ℕ)
    (items : List α) (t : Fin T) : List α :=
  (List.ofFn (fun g : Fin ((20*(w+1)+2)^d) =>
    atTick (group (key w cost) items (finFunctionFinEquiv.symm g)) t)).flatten

@[to_additive]
private theorem prod_concat {α M : Type*} [CommMonoid M] {n : ℕ} (xs : Fin n → List α) (f : α → M) :
    (((List.ofFn xs).flatten).map f).prod = ∏ i, ((xs i).map f).prod := by
  simp [List.map_flatten, List.prod_flatten, List.map_ofFn, List.prod_ofFn, Function.comp_def]

@[to_additive]
private theorem prod_atTick {α M : Type*} [CommMonoid M] {T : ℕ} (xs : List α) (f : α → M)
    (t : Fin T) : ((atTick xs t).map f).prod =
      ∏ i : Fin xs.length, if i.val ≡ t.val [MOD T] then f xs[i] else 1 := by
  rw [atTick, prod_concat]
  apply Finset.prod_congr rfl
  intro i _
  split <;> simp_all

@[to_additive]
private theorem prod_factors {α M : Type*} [CommMonoid M] {T d : ℕ} (w : ℕ)
    (cost : α → Fin d → ℕ) (items : List α) (f : α → M) (t : Fin T) :
    ((factors w cost items t).map f).prod =
      ∏ g : Key w d, ((atTick (group (key w cost) items g) t).map f).prod := by
  rw [factors, prod_concat]
  apply Fintype.prod_equiv finFunctionFinEquiv.symm
  intro g
  rfl

@[to_additive]
private theorem prod_by_class {α κ M : Type*} [Fintype κ] [DecidableEq κ] [CommMonoid M]
    (tag : α → κ) (items : List α) (f : α → M) :
    (∏ g, ((group tag items g).map f).prod) = (items.map f).prod := by
  classical
  induction items with
  | nil => simp [group]
  | cons a xs ih =>
    have step (g : κ) : ((group tag (a::xs) g).map f).prod =
        (if tag a=g then f a else 1) * ((group tag xs g).map f).prod := by
      by_cases h : tag a = g <;> simp [group,h]
    simp only [step,Finset.prod_mul_distrib,ih,List.map_cons,List.prod_cons]
    simp

@[to_additive]
private theorem prod_all_atTick {α M : Type*} [CommMonoid M] {T : ℕ} (ht : 0<T)
    (xs : List α) (f : α → M) :
    (∏ t : Fin T, ((atTick xs t).map f).prod) = (xs.map f).prod := by
  classical
  let slot (i : Fin xs.length) : Fin T := ⟨i.val%T, Nat.mod_lt _ ht⟩
  have test (i : Fin xs.length) (t : Fin T) : i.val ≡ t.val [MOD T] ↔ slot i=t := by
    rw [Nat.ModEq, Nat.mod_eq_of_lt t.isLt, Fin.ext_iff]
  simp_rw [prod_atTick, test]
  rw [Finset.prod_comm]
  simp only [Finset.prod_ite_eq, Finset.mem_univ, ite_true]
  rw [← List.prod_ofFn, List.ofFn_comp' (fun i : Fin xs.length => xs[i]) f ]
  exact congrArg (fun l => (l.map f).prod) (List.ofFn_getElem (xs:=xs))

/-- Each original factor is computed once, even when several occurrences have
the same value. The identity applies to evaluated weights over every field. -/
@[to_additive]
theorem prod_factors_all {α M : Type*} [CommMonoid M] {T d : ℕ} (ht : 0<T) (w : ℕ)
    (cost : α → Fin d → ℕ) (items : List α) (f : α → M) :
    (∏ t : Fin T, ((factors w cost items t).map f).prod) = (items.map f).prod := by
  simp_rw [prod_factors]
  rw [Finset.prod_comm]
  simp_rw [prod_all_atTick ht]
  exact prod_by_class _ _ _

/-- The number of work units, pairs or advice bits in the emitted factor
list is exactly the load used in the analytic allocation estimate. -/
theorem sum_factors_eq_tickLoad {α : Type*} {T d : ℕ} (w : ℕ) (cost : α → Fin d → ℕ)
    (items : List α) (j : Fin d) (t : Fin T) :
    (((factors w cost items t).map (fun a => cost a j)).sum : ℝ) = tickLoad w cost items j t := by
  classical
  push_cast
  rw [List.map_map, sum_factors]
  unfold tickLoad
  refine Finset.sum_congr rfl fun g _ => ?_
  let xs := group (key w cost) items g
  rw [sum_atTick]
  unfold RoundRobin.selected
  rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≡ t.val [MOD T]
  · simp only [ite_eq_left h]
    change (cost xs[i] j : ℝ) = ((xs[i.val]?).map (fun x => (cost x j : ℝ))).getD 0
    rw [getElem?_pos xs i.val i.isLt]
    rfl
  · simp [h]

end Hierarchy.FactorAllocation

end OAI
