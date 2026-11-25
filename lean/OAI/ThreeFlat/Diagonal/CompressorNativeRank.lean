import OAI.ThreeFlat.RAM.DescriptorExpr
import Mathlib.Data.Finset.Sort

namespace OAI
/-! # Native rank and selection in bounded lists of incident edge identifiers

Zero denotes an invalid candidate. The incoming and outgoing lists can
contain duplicate visits to an edge; the circuit counts its last visit.
The rank is the number of distinct nonzero codes strictly below the key.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Rank
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.DescriptorExpr
open scoped Fin.NatCast
variable {w k n : ℕ}

def contains (a : Term w k n) : List (Term w k n) → Term w k n
  | [] => .literal 0
  | x::xs => .select .eq a x (.literal 1) (contains a xs)

def below (xs : List (Word w)) (key : Word w) : Finset (Word w) :=
  xs.toFinset.filter fun x => x ≠ 0 ∧ x < key

def contribution (key x : Term w k n) (tail : List (Term w k n)) : Term w k n :=
  .select .eq x (.literal 0) (.literal 0)
    (.select .lt x key (.select .eq (contains x tail) (.literal 0) (.literal 1) (.literal 0))
      (.literal 0))

def rank (key : Term w k n) : List (Term w k n) → Term w k n
  | [] => .literal 0
  | x::xs => .binary .add (rank key xs) (contribution key x xs)

def pick (key : Term w k n) (all : List (Term w k n)) : List (Term w k n) → Term w k n
  | [] => .literal 0
  | x::xs =>
    let available := Term.select .eq x (.literal 0) (.literal 0)
      (.select .eq (rank x all) key (.literal 1) (.literal 0))
    .select .eq available (.literal 1) x (pick key all xs)

variable (pub : Fin k → Word w) (m : Memory w) (vs : Fin n → Word w)

abbrev val (e : Term w k n) := e.eval pub m vs
abbrev vals (xs : List (Term w k n)) := xs.map (val pub m vs)

theorem eval_contains (e : Term w k n) (xs : List (Term w k n)) :
    val pub m vs (contains e xs) = if val pub m vs e ∈ vals pub m vs xs then 1 else 0 := by
  induction xs with
  | nil => simp [contains,val,vals]
  | cons x xs ih =>
    by_cases eq : e.eval pub m vs = x.eval pub m vs <;>
      simp [contains,val,vals,Comparison.test,eq,ih]

theorem below_cons (key x : Word w) (xs : List (Word w)) :
    (below (x::xs) key).card = (below xs key).card +
      if x ≠ 0 ∧ x < key ∧ x ∉ xs then 1 else 0 := by
  by_cases h : x ≠ 0 ∧ x < key
  · by_cases seen : x ∈ xs
    · have hm : x ∈ xs.toFinset := List.mem_toFinset.mpr seen
      simp [below,Finset.insert_eq_of_mem hm,h,seen]
    · have hn : x ∉ below xs key := by simp [below,seen]
      simp only [below,List.toFinset_cons,Finset.filter_insert,ite_eq_left h]
      change (insert x (below xs key)).card = _
      rw [Finset.card_insert_of_notMem hn]
      simp [below,h.1,h.2,seen]
  · simp [below,Finset.filter_insert,h,show ¬ (x ≠ 0 ∧ x < key ∧ x ∉ xs) from fun e => h ⟨e.1,e.2.1⟩]

private theorem wordCast_add (a b : ℕ) : ((a+b : ℕ) : Word w) = (a : Word w)+(b : Word w) :=
  Fin.ext (Nat.add_mod ..)

theorem eval_rank (one : (1 : Word w) ≠ 0) (key : Term w k n) (xs : List (Term w k n)) :
    val pub m vs (rank key xs) = ((below (vals pub m vs xs) (val pub m vs key)).card : Word w) := by
  induction xs with
  | nil => simp [val,vals,rank,below]
  | cons x xs ih =>
    change (Term.binary .add (rank key xs) (contribution key x xs)).eval pub m vs =
      ((below (val pub m vs x :: vals pub m vs xs) (val pub m vs key)).card : Word w)
    rw [Term.eval_binary,below_cons,wordCast_add]
    change val pub m vs (rank key xs) + _ = _
    rw [ih]
    congr 1
    by_cases zero : val pub m vs x = 0 <;>
      by_cases lt : val pub m vs x < val pub m vs key <;>
        by_cases seen : val pub m vs x ∈ vals pub m vs xs <;>
          simp [contribution,Comparison.test,val,eval_contains,zero,lt,seen,one]; rfl

def chosen (all : List (Word w)) (key : Word w) : List (Word w) → Word w
  | [] => 0
  | x::xs => if x ≠ 0 ∧ ((below all x).card : Word w) = key then x else chosen all key xs

theorem eval_pick (one : (1 : Word w) ≠ 0) (key : Term w k n)
    (all candidates : List (Term w k n)) :
    val pub m vs (pick key all candidates) =
      chosen (vals pub m vs all) (val pub m vs key) (vals pub m vs candidates) := by
  induction candidates with
  | nil => rfl
  | cons x xs ih =>
    change val pub m vs (pick key all (x::xs)) = chosen _ _ (val pub m vs x :: vals pub m vs xs)
    by_cases zero : val pub m vs x = 0 <;>
      by_cases equal : ((below (vals pub m vs all) (val pub m vs x)).card : Word w) = val pub m vs key <;>
        simp [pick,chosen,Comparison.test,val,eval_rank pub m vs one,zero,equal,ih,one.symm]

end ThreeFlat.Diagonal.CompressorPacking.Native.Rank

end OAI
