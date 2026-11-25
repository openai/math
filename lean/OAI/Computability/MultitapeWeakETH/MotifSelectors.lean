import OAI.Computability.MultitapeWeakETH.MotifFields
import OAI.Computability.MultitapeWeakETH.SiteCheck

/-! # Decoding the motif selectors carried above a supply payload -/

namespace OAI.Computability.MultitapeWeakETH.MotifFields

open IntegerMultiplication Code VPVNP StackInterpreter MotifSelector
noncomputable section

/-- Every copy reads its own fixed-width tag, including when that width is zero. -/
def tags (a : ℕ) (q : (Bits.Word × Tally) × Tally) :=
  (Iter.lineup q.2).map fun j => copy a (q.1,j)

theorem tags_poly (a : ℕ) : Poly (tags a) :=
  (Easy.fst.poly.pair (Easy.snd.poly.compose Iter.poly_line)).compose (Poly.push ([],[]) [] (copy_poly a))

theorem tags_eq {u a v : ℕ} (x : Fin (v+u*a) → Bool) :
    tags a ((List.ofFn x,tally v),tally u) = List.ofFn fun i : Fin u => Label.mk (MotifEntry.readTag x i) := by
  simp only [tags,Iter.lined,List.map_ofFn,Function.comp_def]
  exact congrArg List.ofFn (funext fun i => Label.ext (copy_tag x i))

variable {S : Type} [Fintype S] {a : ℕ} (table : List S) (code : S ↪ Word a)

/-- A missing tag rejects the entire sequence, while repeated selectors retain their
positions. Each search is in the same finite motif table for every input size. -/
def decodeTags (ts : List (Label (Word a))) : Option (List (Label S)) :=
  let val (x : Label (Word a)) := (MotifEntry.decode table code x.val).map Label.mk
  bif ts.any (fun x => (val x).isNone) then none else some ((ts.map (fun x => (val x).toList)).flatten)

theorem decodeTags_poly : Poly (decodeTags table code) := by
  let val (x : Label (Word a)) := (MotifEntry.decode table code x.val).map Label.mk
  have bad := CNFNetwork.SiteCheck.any_poly (fun x => (val x).isNone) (Easy.finite _).poly
  have names := ((Poly.maps _ (Easy.finite (fun x => (val x).toList)).poly).compose Easy.flatten.poly).compose Easy.some.poly
  exact Poly.choose bad (Code.Poly.const none) names

omit [Fintype S] in
theorem decodeTags_eq {u : ℕ} (t : Fin u → Word a) :
    decodeTags table code (List.ofFn fun i => Label.mk (t i)) =
      (MotifEntry.selectors? table code t).map (fun seq => List.ofFn fun i => Label.mk (seq i)) := by
  let d (i : Fin u) := MotifEntry.decode table code (t i)
  by_cases h : ∀ i, (d i).isSome = true
  · let seq (i : Fin u) := (d i).get (h i)
    have e (i : Fin u) : d i = some (seq i) := (Option.some_get (h i)).symm
    have tags : MotifEntry.selectors? table code t = some seq := by
      simp only [MotifEntry.selectors?,Vector.getElem_ofFn]
      exact dite_eq_left h
    rw [tags]
    have none : ((List.ofFn fun i => Label.mk (t i)).any (fun x => ((MotifEntry.decode table code x.val).map Label.mk).isNone)) = false := by
      apply List.any_eq_false.mpr
      intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      change ¬ ((d i).map Label.mk).isNone = true
      simp [e]
    have found (i : Fin u) : MotifEntry.decode table code (t i) = some (seq i) := e i
    simp only [decodeTags,none,Bool.cond_false,List.map_ofFn,Function.comp_def,found,Option.map_some,Option.toList_some,Option.some.injEq]
    rw [show (List.ofFn fun i : Fin u => [Label.mk (seq i)]) = (List.ofFn fun i => Label.mk (seq i)).map (fun x => [x]) by simp only [List.map_ofFn,Function.comp_def]]
    have join (xs : List (Label S)) : (xs.map (fun x => [x])).flatten = xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih => simp only [List.map_cons,List.flatten_cons,List.singleton_append,ih]
    exact join _
  · obtain ⟨i,invalid⟩ := not_forall.mp h
    have miss : d i = none := by cases hit : d i <;> simp_all
    have tags : MotifEntry.selectors? table code t = none := by
      simp only [MotifEntry.selectors?,Vector.getElem_ofFn]
      exact dite_eq_right h
    rw [tags]
    have someBad : ((List.ofFn fun j => Label.mk (t j)).any (fun x => ((MotifEntry.decode table code x.val).map Label.mk).isNone)) = true := by
      apply List.any_eq_true.mpr
      exact ⟨⟨t i⟩,List.mem_ofFn.mpr ⟨i,rfl⟩,by change ((d i).map Label.mk).isNone=true; simp [miss]⟩
    simp only [decodeTags,someBad,Bool.cond_true,Option.map_none]

end
end OAI.Computability.MultitapeWeakETH.MotifFields
