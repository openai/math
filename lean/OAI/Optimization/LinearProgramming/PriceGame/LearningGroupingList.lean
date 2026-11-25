import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! A canonical sorted, duplicate-free list and size-preserving filtering on the binary stack. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)

def selected {α : Type*} : List (Bool × α) → List α
  | [] => []
  | (b,a)::xs => if b then a::selected xs else selected xs

theorem selected_map {α : Type*} (p : α → Bool) (xs : List α) :
    selected (xs.map fun a => (p a,a)) = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : p a <;> simp [h,selected,ih]

private def addFlagged {α : Type*} (v : (Bool × α) × List α) : List α :=
  if v.1.1 then v.1.2 :: v.2 else v.2

private theorem fold_flags {α : Type*} (xs : List (Bool × α)) (a : List α) :
    xs.foldl (fun acc v => addFlagged (v,acc)) a = (selected xs).reverse ++ a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨b,v⟩ := x
    rw [List.foldl_cons, ih]
    cases b <;> simp [addFlagged, selected, List.append_assoc]

private theorem flagged_words {α : Type} (ea : α → List Bool) (xs : List (Bool × α)) :
    (listCode ea (selected xs)).length ≤ (listCode (prodCode boolCode ea) xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨b,v⟩ := x
    cases b <;> simp only [selected, Bool.false_eq_true, ite_false, ite_true, listCode_length_cons,
      prodCode,pairBits_length] <;> omega

/-- Keep the marked entries in their original order, traversing and charging the encoded list. -/
noncomputable def selectedP {α : Type} (ea : α → List Bool) (d : α) :
    Procedure (listCode (prodCode boolCode ea)) (listCode ea) selected := by
  let item := prodCode boolCode ea
  let old := Procedure.second item (listCode ea)
  let inp := Procedure.first item (listCode ea)
  let b := (Procedure.first boolCode ea).comp inp
  let val := (Procedure.second boolCode ea).comp inp
  let step : Procedure (prodCode item (listCode ea)) (listCode ea) addFlagged :=
    Procedure.conditional b ((Procedure.listCons ea).comp (val.pair old)) old
  let fold := Procedure.foldList (false,d) step Polynomial.X (by
    intro xs acc i
    rw [fold_flags, Polynomial.eval_X]
    have ha := listCode_length_append ea (selected (xs.take i)).reverse acc
    rw [listCode_length_rev] at ha
    have hb := (flagged_words ea (xs.take i)).trans (listCode_length_take_le item i xs)
    omega)
  let start := (Procedure.identity (listCode item)).pair (Procedure.constant (listCode item) (listCode ea) [])
  apply ((Procedure.listReverse ea d).comp (fold.comp start)).congrFun
  intro xs
  change ((xs.foldl (fun acc v => addFlagged (v,acc)) []).reverse) = selected xs
  rw [fold_flags, List.append_nil, List.reverse_reverse]

/-- The two filters partition all values except those equal to the newly inserted key. -/
def insertKey {α : Type*} [LinearOrder α] (a : α) (xs : List α) : List α :=
  xs.filter (fun b => decide (b<a)) ++ a :: xs.filter (fun b => decide (a<b))

theorem mem_insertKey {α : Type*} [LinearOrder α] (a b : α) (xs : List α) :
    b ∈ insertKey a xs ↔ b = a ∨ b ∈ xs := by
  simp only [insertKey,List.mem_append,List.mem_filter,decide_eq_true_eq,List.mem_cons]
  rcases lt_trichotomy b a with h|h|h <;> grind

private theorem pairwise_insertKey {α : Type*} [LinearOrder α] (a : α) (xs : List α)
    (hs : xs.Pairwise (· < ·)) : (insertKey a xs).Pairwise (· < ·) := by
  rw [insertKey, List.pairwise_append, List.pairwise_cons]
  refine ⟨hs.filter _, ⟨?_,hs.filter _⟩, ?_⟩
  · intro y hy
    exact of_decide_eq_true (List.mem_filter.mp hy).2
  · intro x hx y hy
    have hxa := of_decide_eq_true (List.mem_filter.mp hx).2
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hxa
    · exact hxa.trans (of_decide_eq_true (List.mem_filter.mp hy).2)

def sortedUnique {α : Type*} [LinearOrder α] (xs : List α) : List α :=
  xs.foldl (fun ys x => insertKey x ys) []

private theorem fold_keys {α : Type*} [LinearOrder α] (xs ys : List α) (hs : ys.Pairwise (· < ·)) :
    (xs.foldl (fun acc x => insertKey x acc) ys).Pairwise (· < ·) ∧
      ∀ a, a ∈ xs.foldl (fun acc x => insertKey x acc) ys ↔ a ∈ xs ∨ a ∈ ys := by
  induction xs generalizing ys with
  | nil => simpa using hs
  | cons a xs ih =>
    obtain ⟨hp, hm⟩ := ih (insertKey a ys) (pairwise_insertKey a ys hs)
    refine ⟨hp, fun x => ?_⟩
    rw [List.foldl_cons,hm,mem_insertKey,List.mem_cons]
    tauto

theorem sortedUnique_eq_sort {α : Type*} [LinearOrder α] (xs : List α) :
    sortedUnique xs = xs.toFinset.sort := by
  obtain ⟨hp,hm⟩ := fold_keys xs [] (.nil)
  apply hp.eq_of_mem_iff xs.toFinset.sortedLT_sort.pairwise
  intro a
  simpa using hm a

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
