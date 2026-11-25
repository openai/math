import OAI.Computability.IntegerMultiplication.Strip.Profile

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fix
open Strip Code Optic
variable {O A B X : Type} [DecidableEq X] [Codec A]
variable {s : Series O} {t : Series B} (g : File s X t)
def slot (x : O) := (g.focus x).1
def sheet (bad : X→Bool) (ids : X→Key) (x : O) : Info :=
  (bad (slot g x),ids (slot g x))

omit [Codec A] in
theorem partial_agg
    (bad : X→Bool) (ids : X→Key) (f : O→A) (k : Key) :
    draw k (batch true (sheet g bad ids) f s)=
      (s.tab (fun x => if bad (slot g x)=true ∧ ids (slot g x)=k then [f x] else [])).flatten := by
  unfold draw batch stamps Ribbon.read Series.tab
  induction s.explore with
  | nil => rfl
  | cons x l ih =>
    by_cases e:bad (slot g x)=true <;> by_cases r:ids (slot g x)=k <;>
      simp [sheet,List.map_cons,List.flatten_cons,Ribbon.keep,e,r,leaf,-List.map_map] <;> exact ih
omit [Codec A] in
theorem crystal
    (bad : X→Bool) (ids : X→Key) (hi : Function.Injective ids) (f : O→A) (x : X) (h : bad x=true) :
    draw (ids x) (batch true (sheet g bad ids) f s)=
    t.tab (fun i => f (g.focus.symm (x,i))) := by
  rw [partial_agg, ← g.sees x f]
  simp only [hi.eq_iff,Function.comp_def,slot]
  have e : (fun i : O => if bad (g.focus i).1=true ∧ (g.focus i).1=x then [f i] else []) =
      (fun i : O => if (g.focus i).1=x then [f i] else []) := by
    funext i; by_cases e:(g.focus i).1=x <;> simp [*]
  rw [e]; rfl
omit [Codec A] in
theorem unrealized
    (bad : X→Bool) (ids : X→Key) (f : O→A) (k)
    (h : ¬∃ x,bad x=true ∧ ids x=k) :
    draw k (batch true (sheet g bad ids) f s)=[] := by
  rw [partial_agg]
  have e : (fun x : O => if bad (slot g x)=true ∧ ids (slot g x)=k then [f x] else []) =
      fun _=> [] := funext (fun x => ite_eq_right (fun z => h ⟨_,z⟩))
  rw [e]; unfold Series.tab
  induction s.explore <;> simp_all

variable (q : X≃X) (bad : X→Bool) (ids : X→Key) (hi : Function.Injective ids)
variable (f : O→A)
-- correction support-only if external x good
variable (S : ∀ x,bad x=false → q x=x)
include S
omit [DecidableEq X] in
theorem invert x (h : bad x=false) : q.symm x=x := by
  apply q.injective
  simpa only [Equiv.apply_symm_apply] using (S x h).symm
omit [DecidableEq X] in
theorem tail_works x : bad (q x)=bad x := by
  cases e : bad x
  · rw [S x e,e]
  cases h: bad (q x)
  · have t := invert q bad S _ h
    rw [Equiv.symm_apply_apply] at t
    rw [← t,e] at h
    contradiction
  rfl

include hi
omit [Codec A] in
theorem intend (k) :
    draw k (batch true (sheet g bad (ids ∘ q)) f s) =
    draw k (batch true (sheet g bad ids) (travel (Optic.field g.focus q) f) s) := by
  by_cases d : ∃ x,bad x=true ∧ ids x=k
  · obtain ⟨x,e,rfl⟩ := (show ∃ x,bad x=true ∧ k=ids x from by obtain ⟨x,e,h⟩:=d; exact ⟨x,e,h.symm⟩)
    rw [crystal g _ _ hi _ _ e, show ids x=(ids ∘ q) (q.symm x) by simp]
    have h : bad (q.symm x)=true := by rw [← tail_works q bad S,Equiv.apply_symm_apply,e]
    rw [crystal g _ _ (hi.comp q.injective) _ _ h]
    simp [travel]
  rw [unrealized g _ _ _ _ d] -- looks for LHS? underscore infer wrong
  apply unrealized
  rintro ⟨x,e,f⟩
  exact d ⟨_,tail_works q bad S _ |>.trans e,f⟩

omit hi [Codec A] in
theorem untreated :
    parcel (batch false (sheet g bad (ids ∘ q)) f s) =
    parcel (batch false (sheet g bad ids) (travel (Optic.field g.focus q) f) s) := by
  rw [binValue,binValue]
  unfold Ribbon.read sheet Series.tab
  induction s.explore with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons,List.flatten_cons,ih]
    congr 1
    cases e : bad (slot g x)
    · obtain ⟨⟨i,k⟩,rfl⟩ := g.focus.symm.surjective x
      simp only [slot,Equiv.apply_symm_apply] at e
      simp [Ribbon.keep,travel,invert q bad S i e]
    simp [Ribbon.keep] -- e slot but simp unfolding
variable [Fintype O] [Fintype X] [Fintype B] [DecidableEq O]
omit hi S in
theorem filter_rate :
    (s.explore.filter fun i => bad (slot g i)).length =
      (Finset.univ.filter fun i => bad i).card * t.count := by
  classical
  -- careful DecidableEq O
  let e := fun i : O => bad (slot g i)
  let p : Finset O := (Finset.univ.filter fun i => e i)
  let r : Finset X := Finset.univ.filter fun i => bad i
  have z : (s.explore.filter e).length=p.card := by
    rw [← List.toFinset_card_of_nodup (s.nodup.filter _)]
    congr 1
    ext i; simp [p,s.complete, Finset.mem_filter]
  rw [z]
  rw [Series.total]
  rw [← Finset.card_univ (α:=B), ← Finset.card_product]
  apply Finset.card_equiv g.focus
  intro i
  simp [p,e,slot]
  change i ∈ (Finset.univ.filter (fun x : O => bad (g.focus x).1 = true)) ↔
    bad (g.focus i).1 = true
  simp

end Fix
namespace Strip
variable {I J K L : Type} [DecidableEq I] [DecidableEq J]
variable {A : Type} {s : Series A} {k : Series K}
namespace File
def selectCongr (f : File s I k) (e : I≃J) : File s J k where
  focus := f.focus.trans (e.prodCongr (Equiv.refl K))
  sees {_} i v := by
    have t := f.sees (e.symm i) v
    suffices h : intercept
        (Prod.fst ∘ ⇑(f.focus.trans (e.prodCongr (Equiv.refl K)))) i v =
          intercept (Prod.fst ∘ ⇑f.focus) (e.symm i) v by
      rw [h,t]
      rfl
    funext x
    simp [intercept, Equiv.eq_symm_apply]
end File
end Strip

end IntegerMultiplication
end Computability
end OAI
