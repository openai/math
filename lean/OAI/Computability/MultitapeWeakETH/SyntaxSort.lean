import OAI.Computability.MultitapeWeakETH.RankProgram
import Mathlib.Data.Finset.Sort

/-! # Polynomial-time sorting of the raw leaf's clauses and literals -/

namespace OAI.Computability.MultitapeWeakETH.SyntaxSort

open IntegerMultiplication.Code
open scoped List

variable {X : Type} (lt : X × X → Bool)

private def splice (xs : List X) (x : X) :=
  xs.filter (fun y => lt (y,x)) ++ x :: xs.filter (fun y => !(lt (y,x)))

private theorem splice_perm (xs : List X) (x : X) : splice lt xs x ~ x::xs :=
  List.perm_middle.trans ((List.filter_append_perm (fun y => lt (y,x)) xs).cons x)

/-- No comparator assumptions are needed for the physical time bound:
each comparison sends the earlier entry to exactly one side. -/
def arrange (xs : List X) := xs.foldl (splice lt) []

private theorem fold_perm (xs acc : List X) : xs.foldl (splice lt) acc ~ acc++xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    exact (ih (splice lt acc x)).trans (((splice_perm lt acc x).append_right xs).trans List.perm_middle.symm)

theorem arrange_poly [Codec X] [Inhabited X] (p : Poly lt) : Poly (arrange lt) := by
  have part (test : X × X → Bool) (hp : Poly test) :
      Poly (fun q : List X × X => q.1.filter fun y => test (y,q.2)) := by
    have row : Poly (fun q : X × X => bif test q.swap then [q.2] else []) :=
      Poly.choose (Easy.exchange.poly.compose hp) (by fun_prop) (IntegerMultiplication.Code.Poly.const ([] : List X))
    have take := (Easy.exchange.poly.compose (Poly.push default default row)).compose Easy.flatten.poly
    convert take using 1
    funext q
    rcases q with ⟨xs,x⟩
    induction xs with
    | nil => rfl
    | cons y xs ih =>
      change (y::xs).filter _ = (bif test (y,x) then [y] else []) ++ _
      cases eq : test (y,x) <;> simpa [List.filter,eq,polyPush] using congrArg (fun t => (bif test (y,x) then [y] else []) ++ t) ih
  have hp : Poly (fun q : List X × X => splice lt q.1 q.2) :=
    (part lt p).app ((Easy.snd.poly.pair (part _ (p.compose Iter.negate.poly))).compose Easy.cons.poly)
  have loop := Poly.fold_left hp 1 1 (fun ⟨xs,acc⟩ l h => ?_)
  exact (Poly.identity.pair (IntegerMultiplication.Code.Poly.const ([] : List X))).compose loop
  have perm := fold_perm lt l acc
  have eqsize {a b : List X} (pm : a~b) : size a=size b := by
    induction pm with
    | nil => rfl
    | cons _ _ ih => simp [ih]
    | swap => simp; omega
    | trans _ _ ih ij => exact ih.trans ij
  have e := size_append_right acc l
  obtain ⟨rest,hr⟩ := h
  change l++rest=xs at hr
  have b := size_append_right l rest
  rw [hr] at b
  have ge : 0 < size rest := Nat.zero_lt_of_lt (duration _)
  change size (l.foldl (splice lt) acc) ≤ 1*(size xs+size acc+1+1)^1
  rw [eqsize perm,pow_one,one_mul]
  omega

variable {A : Type} [LinearOrder A]
private def insertNum (xs : List A) (x : A) := splice (fun p : A×A => decide (p.1<p.2)) xs x

private theorem insert_sorted {xs : List A} (h : xs.Pairwise (·≤·)) (x : A) :
    (insertNum xs x).Pairwise (·≤·) := by
  unfold insertNum splice
  apply List.pairwise_append.mpr
  refine ⟨h.filter _,List.pairwise_cons.mpr ⟨?_,h.filter _⟩,?_⟩
  · intro y hy
    simpa using (List.mem_filter.mp hy).2
  · intro y hy z hz
    have low : y < x := of_decide_eq_true (List.mem_filter.mp hy).2
    rcases List.mem_cons.mp hz with rfl | hz
    · exact low.le
    · exact low.le.trans (by simpa using (List.mem_filter.mp hz).2)

private theorem num_sort (xs : List A) (nodup : xs.Nodup) :
    xs.foldl insertNum [] = xs.toFinset.sort (·≤·) := by
  have order (ys acc : List A) (h : acc.Pairwise (·≤·)) : (ys.foldl insertNum acc).Pairwise (·≤·) := by
    induction ys generalizing acc with
    | nil => exact h
    | cons y ys ih => exact ih _ (insert_sorted h y)
  have p : xs.foldl insertNum [] ~ xs := by
    change xs.foldl (splice (fun q : A×A => decide (q.1<q.2))) [] ~ xs
    simpa only [List.nil_append] using fold_perm (fun q : A×A => decide (q.1<q.2)) xs []
  have e := (List.toFinset_sort (r:=(·≤·)) (p.nodup_iff.mpr nodup)).mpr (order xs [] .nil)
  have same : (xs.foldl insertNum []).toFinset = xs.toFinset := by
    ext a
    simpa only [List.mem_toFinset] using p.mem_iff (a := a)
  rw [same] at e
  exact e.symm

/-- Correctness only needs the comparison to agree on this input's keys.
At width three the comparison may stop after three literal codes. -/
theorem arrange_map (enc : A → X) (ok : A → Prop) (cmp : ∀ a b, ok a → ok b → lt (enc a,enc b)=decide (a<b))
    (xs : List A) (all : ∀ a ∈ xs, ok a) (nodup : xs.Nodup) :
    arrange lt (xs.map enc) = (xs.toFinset.sort (·≤·)).map enc := by
  have insert (acc : List A) (x : A) (hx : ok x) (ha : ∀ a ∈ acc, ok a) :
      splice lt (acc.map enc) (enc x) = (insertNum acc x).map enc := by
    unfold splice insertNum
    simp only [splice,List.map_append,List.map_cons,List.filter_map]
    have left : acc.filter ((fun y => lt (y,enc x)) ∘ enc) =
        acc.filter (fun y => decide (y<x)) :=
      List.filter_congr fun y hy => cmp y x (ha y hy) hx
    have right : acc.filter ((fun y => !(lt (y,enc x))) ∘ enc) =
        acc.filter (fun y => !(decide (y<x))) :=
      List.filter_congr fun y hy => congrArg Bool.not (cmp y x (ha y hy) hx)
    rw [left,right]
  have go (ys acc : List A) (hy : ∀ a ∈ ys, ok a) (ha : ∀ a ∈ acc, ok a) :
      (ys.map enc).foldl (splice lt) (acc.map enc) = (ys.foldl insertNum acc).map enc := by
    induction ys generalizing acc with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.map_cons,List.foldl_cons,insert acc y (hy y List.mem_cons_self) ha]
      refine ih _ (fun _ h => hy _ (List.mem_cons_of_mem _ h)) ?_
      intro q h
      rcases List.mem_cons.mp ((splice_perm _ acc y).mem_iff.mp h) with rfl|h
      · exact hy _ List.mem_cons_self
      · exact ha _ h
  exact (go xs [] all (by simp)).trans (congrArg (List.map enc) (num_sort xs nodup))

end OAI.Computability.MultitapeWeakETH.SyntaxSort
