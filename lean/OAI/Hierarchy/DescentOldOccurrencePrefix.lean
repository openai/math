import OAI.Hierarchy.DescentMatchedPairGraph
import OAI.Hierarchy.DescentOldOccurrenceRank
import OAI.Hierarchy.DescentOrderedOffsetTable

namespace OAI
/-! # Locating each source site in a real thin pack and each thick destination -/

namespace Hierarchy.DescentOldOccurrenceRAM
open DescentPacking ProtocolRAMPortRanks
open scoped Classical BigOperators
noncomputable section
variable {U C : Type*}

theorem list_prefix (f : U → ℕ) (xs : List U) (j : Fin xs.length) :
    «prefix» (fun a : Fin xs.length => f (xs.get a)) Fin.val j = amount f (xs.take j.val) := by
  induction xs with
  | nil => exact Fin.elim0 j
  | cons x xs ih =>
    cases j using Fin.cases with
    | zero => simp [«prefix»,amount]
    | succ j =>
      simp only [«prefix», Finset.sum_filter] at ih ⊢
      change (∑ a : Fin (xs.length+1), if a.val < j.val+1 then f ((x::xs).get a) else 0) = _
      rw [Fin.sum_univ_succ]
      simpa only [Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ, ite_eq_left, ite_true,
        Nat.add_lt_add_iff_right, List.get_cons_zero, List.get_cons_succ',
        List.take_succ_cons, amount, List.map_cons, List.sum_cons] using congrArg (f x + ·) (ih j)

theorem amount_flat (f : U → ℕ) (xs : List (List U)) :
    amount (amount f) xs = amount f xs.flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [amount,List.map_append,List.sum_append] using congrArg (amount f x + ·) ih

private theorem filtered (f : U → ℕ) (p : U → Bool) (xs : List U) :
    amount f (xs.filter p) = amount (fun u => if p u then f u else 0) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [amount,h] at ih ⊢ <;> exact ih

theorem colored_amount {U C : Type} [Fintype U] [Fintype C] [DecidableEq C] (group : U → C)
    (color : U → Bool) (side : Bool) (c : C) (f : U → ℕ) :
    amount f (colorSites group color side c) =
      ∑ u, if group u=c ∧ color u=side then f u else 0 := by
  rw [colorSites,filtered,amount_groupStream]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hc : group u=c <;> by_cases hs : color u=side <;> simp [hc,hs]

theorem take_before {t : ℕ} (ord : U ↪ Fin t) (f : U → ℕ) (pre post : List U) (u : U)
    (sorted : (pre++u::post).Pairwise (fun x y=>ord x < ord y)) :
    amount f pre = amount (fun x => if ord x < ord u then f x else 0) (pre++u::post) := by
  simpa [DescentOrderedWords.paidBefore,amount] using
    DescentOrderedWords.prefix_eq (fun _ : U => ()) f ord sorted

private theorem split_at_get (xs : List U) (i : Fin xs.length) :
    xs.take i.val ++ xs.get i :: xs.drop (i.val+1) = xs :=
  (congrArg (fun tail => xs.take i.val ++ tail) (List.getElem_cons_drop i.isLt)).trans
    (List.take_append_drop i.val xs)

theorem middle_site {t : ℕ} (ord : U ↪ Fin t) (f : U → ℕ) (xs : List U)
    (sorted : xs.Pairwise (fun x y=>ord x < ord y)) (i : Fin xs.length) :
    «prefix» (fun a : Fin xs.length => f (xs.get a)) Fin.val i =
      amount (fun x => if ord x < ord (xs.get i) then f x else 0) xs := by
  rw [list_prefix]
  have split_ : xs.take i.val ++ xs.get i :: xs.drop (i.val+1)=xs := split_at_get xs i
  have lemma_ := take_before ord f (xs.take i.val) (xs.drop (i.val+1)) (xs.get i) (split_.symm ▸ sorted)
  rwa [split_] at lemma_

theorem nested_site {t : ℕ} (ord : U ↪ Fin t) (f : U → ℕ) (blocks : List (List U))
    (sorted : blocks.flatten.Pairwise (fun x y => ord x < ord y))
    (j : Fin blocks.length) (i : Fin (blocks.get j).length) :
    «prefix» (fun z : Fin blocks.length => amount f (blocks.get z)) Fin.val j +
      «prefix» (fun z : Fin (blocks.get j).length => f ((blocks.get j).get z)) Fin.val i =
      amount (fun x => if ord x < ord ((blocks.get j).get i) then f x else 0) blocks.flatten := by
  let outer := (blocks.take j.val).flatten
  let inner := (blocks.get j).take i.val
  let u := (blocks.get j).get i
  let post := (blocks.get j).drop (i.val+1) ++ (blocks.drop (j.val+1)).flatten
  have flat : outer ++ blocks.get j ++ (blocks.drop (j.val+1)).flatten = blocks.flatten := by
    have seq : blocks.take j.val ++ blocks.get j :: blocks.drop (j.val+1)=blocks := split_at_get blocks j
    simpa only [List.flatten_append,List.flatten_cons,List.append_assoc,outer] using congrArg List.flatten seq
  have total : (outer++inner) ++ u::post=blocks.flatten := by
    have inside : inner ++ u :: (blocks.get j).drop (i.val+1)=blocks.get j :=
      split_at_get (blocks.get j) i
    calc
      (outer++inner) ++ u::post =
          (outer ++ (inner ++ u :: (blocks.get j).drop (i.val+1))) ++ (blocks.drop (j.val+1)).flatten := by
            simp only [post,List.append_assoc,List.cons_append]
      _ = blocks.flatten := by rw [inside,flat]
  rw [list_prefix,list_prefix,amount_flat]
  have first := take_before ord f (outer++inner) post u (total.symm ▸ sorted)
  rw [total] at first
  simpa only [amount,List.map_append,List.sum_append,outer,inner,u] using first

end
end Hierarchy.DescentOldOccurrenceRAM

end OAI
