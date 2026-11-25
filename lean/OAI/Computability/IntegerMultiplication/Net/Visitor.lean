import OAI.Computability.IntegerMultiplication.Net.Scene
import OAI.Computability.IntegerMultiplication.Net.Pins

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Motif.Halo
open Finset Matrix Tensor Plate Place
variable {T J R : Type} [DecidableEq T] [DecidableEq J] [Fintype J] [CommRing R]
variable (P : T → Mat J R) (cond : Chart J R → Prop)
variable (adj : T → T → Prop)
variable (supply : ∀ t u, t=u ∨ adj t u → Nonempty (License T J R cond P t u))

include supply in
theorem host (j : S) (p : Sub T) (t u : T) (e : t=u ∨ adj t u) :
    ∃ (idx : S → T → J) (Z : S → Chart J R), (∀ i, cond (Z i)) ∧
      grant idx P Z (fill j p t) ∧ grant idx P Z (fill j p u) ∧
      (t≠u → idx j t ≠ idx j u) := by
  have ha (i : S) : fill j p t i = fill j p u i ∨ adj (fill j p t i) (fill j p u i) := by
    by_cases h : i=j
    · subst i; simpa
    exact Or.inl (fill_other _ _ _ _ h)
  let w := fun i => Classical.choice (supply _ _ (ha i))
  refine ⟨fun i => (w i).identify, fun i => (w i).board, fun i => (w i).safe,
    fun i => (w i).pin _ (Or.inl rfl), fun i => (w i).pin _ (Or.inr rfl), ?_⟩
  simpa using (w j).distinct

/-- edges have a certificate for oriented residual with the same size accounting -/
def decorated (u v : Place T) :=
  limit u ∧ limit v ∧
  ∃ (idx : S → T → J) (Z : S → Chart J R),
    (∀ i, cond (Z i)) ∧ material idx P Z u ∧ material idx P Z v ∧
      (canvas idx u ⊆ canvas idx v ∨ canvas idx v ⊆ canvas idx u)

-- index relative containment
omit [DecidableEq T] in
theorem y_stowed (idx : S → T → J) (j : S) (p : Sub T) (t : T) :
    canvas idx (.ybox j.val (fill j p t)) ⊆ canvas idx (.low j p) := by
  intro x e
  obtain ⟨e1,e2⟩ := mem_sdiff.mp e
  refine mem_sdiff.mpr ⟨end_in idx j p t e1,?_⟩
  intro hit; apply e2
  rw [← overlap idx j p t]
  exact mem_inter.mpr ⟨e1,hit⟩

omit [DecidableEq T] [DecidableEq J] in
theorem between (idx : S → T → J) (j : S) (p : Sub T) (t : T) :
    grain idx (fill j p t) ⊆ tile idx (wide j p) :=
  (grain_slab idx j p t).trans (minus_in idx j p)
omit [DecidableEq T] in
theorem clean_y (idx : S → T → J) (j : S) (p : Sub T) (t : T) :
    canvas idx (.low j p) ⊆ canvas idx (.ybox (j.val+1) (fill j p t)) := by
  intro x e
  obtain ⟨e1,e2⟩ := mem_sdiff.mp e
  rw [wide_acts j p t] at e1
  exact mem_sdiff.mpr ⟨e1,fun k => e2 (grain_slab idx j p t k)⟩

include supply in
theorem passes [Nonempty T] (post : ∀ t u, adj t u → t≠u) (u v : Place T) (h : road adj u v) :
    u=v ∨ decorated P cond u v := by
  have lm (j : S) : j.val+1 ≤ 3 := by omega
  have lm' (j : S) (a : Keys T) : limit (xEntry j.val a) := by
    unfold xEntry; split <;> simp [limit]
  let t0 := Classical.arbitrary T
  cases h with
  | still l => exact Or.inl rfl
  | entry j p t =>
    obtain ⟨i,Z,c,g,_,_⟩ := host P cond adj supply j p t t (.inl rfl)
    obtain ⟨a,f⟩ := Halo.entry i P Z j _ g
    refine Or.inr ⟨lm' _ _,trivial,i,Z,c,a,support i _ _ _ _ _ g,Or.inl ?_⟩
    rw [f]
    intro x e
    by_cases hit : x ∈ grain i (fill j p t)
    · exact mem_union_right _ hit
    exact mem_union_left _ (y_stowed i j p t (mem_sdiff.mpr ⟨e,hit⟩))
  | fromY j p t =>
    obtain ⟨i,Z,c,g,_,_⟩ := host P cond adj supply j p t t (.inl rfl)
    exact Or.inr ⟨Nat.le_of_lt j.isLt,trivial,i,Z,c,Halo.ybox _ _ _ _ _ g,(commonl _ _ _ _ _ _ g).2,
      Or.inl (y_stowed i j p t)⟩
  | sideStart j p t =>
    obtain ⟨i,Z,c,g,_,_⟩ := host P cond adj supply j p t t (.inl rfl)
    exact Or.inr ⟨trivial,Nat.le_of_lt j.isLt,i,Z,c,empty ..,Halo.ybox _ _ _ _ _ g,
      Or.inl (empty_subset _)⟩
  | side0 j p s t e =>
    obtain ⟨i,Z,c,a,b,_⟩ := host P cond adj supply j p t s (.inr e)
    exact Or.inr ⟨Nat.le_of_lt j.isLt,trivial,i,Z,c,Halo.ybox _ _ _ _ _ b,support _ _ _ _ _ _ a,
      Or.inl ((y_stowed i j p s).trans (subset_union_left))⟩
  | centerStart j p =>
    obtain ⟨i,Z,c,g,_,_⟩ := host P cond adj supply j p t0 t0 (.inl rfl)
    exact Or.inr ⟨trivial,trivial,i,Z,c,empty ..,(commonl _ _ _ _ _ _ g).2, Or.inl (empty_subset _)⟩
  | centerGo j p =>
    obtain ⟨i,Z,c,g,_,_⟩ := host P cond adj supply j p t0 t0 (.inl rfl)
    have r := commonl _ _ _ _ _ _ g
    exact Or.inr ⟨trivial,trivial,i,Z,c,r.2,r.1,Or.inl sdiff_subset⟩
  | centerDrop j p =>
    obtain ⟨i,Z,c,g,_,_⟩ := host P cond adj supply j p t0 t0 (.inl rfl)
    have r := commonl _ _ _ _ _ _ g
    exact Or.inr ⟨trivial,trivial,i,Z,c,r.1,r.2,Or.inr sdiff_subset⟩
  | growX j p t =>
    obtain ⟨i,Z,c,g,_,_⟩ := host P cond adj supply j p t t (.inl rfl)
    exact Or.inr ⟨trivial,trivial,i,Z,c,support _ _ _ _ _ _ g,(commonl _ _ _ _ _ _ g).1,
      Or.inl (union_subset sdiff_subset (between i j p t))⟩
  | growY j p t =>
    obtain ⟨i,Z,c,g,_,_⟩ := host P cond adj supply j p t t (.inl rfl)
    exact Or.inr ⟨trivial,lm j,i,Z,c,(commonl _ _ _ _ _ _ g).2,Halo.ybox _ _ _ _ _ g,
      Or.inl (clean_y i j p t)⟩
  | core j p t u e =>
    -- needs t ≠ u! adjacency should imply this. add hypothesis
    obtain ⟨i,Z,c,a,b,d⟩ := host P cond adj supply j p t u (.inr e)
    refine Or.inr ⟨trivial,lm j,i,Z,c,support _ _ _ _ _ _ a,Halo.ybox _ _ _ _ _ b, Or.inl ?_⟩
    apply union_subset (clean_y i j p u)
    intro x h
    apply mem_sdiff.mpr
    exact ⟨wide_acts j p u ▸ between i j p t h, Finset.disjoint_left.mp (apart i j p t u (d (post t u e))) h⟩
  | sideDone j p t =>
    obtain ⟨i,Z,c,g,_,_⟩ := host P cond adj supply j p t t (.inl rfl)
    refine Or.inr ⟨lm j,trivial,i,Z,c,Halo.ybox _ _ _ _ _ g,(commonl _ _ _ _ _ _ g).1,Or.inl ?_⟩
    simp only [canvas]
    rw [wide_acts j p t]
    exact sdiff_subset
  | finishX j p t =>
    obtain ⟨i,Z,c,g,_,_⟩ := host P cond adj supply j p t t (.inl rfl)
    refine Or.inr ⟨trivial,lm j,i,Z,c,(commonl _ _ _ _ _ _ g).1,Halo.box _ _ _ _ _ g,Or.inl ?_⟩
    simp [canvas, wide_acts j p t]
  | finishQ j p =>
    obtain ⟨i,Z,c,g,_,_⟩ := host P cond adj supply j p t0 t0 (.inl rfl)
    exact Or.inr ⟨trivial,trivial,i,Z,c,(commonl _ _ _ _ _ _ g).1,saturated .., Or.inl (subset_univ _)⟩
  | skip =>
    obtain ⟨i,Z,c,g,_,_⟩ := host P cond adj supply 0 (fun _ => t0) t0 t0 (.inl rfl)
    exact Or.inr ⟨trivial,trivial,i,Z,c,empty ..,saturated .., Or.inl (subset_univ _)⟩

end Net.Motif.Halo

end IntegerMultiplication
end Computability
end OAI
