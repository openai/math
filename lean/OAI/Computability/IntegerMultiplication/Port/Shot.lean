import OAI.Computability.IntegerMultiplication.Port.Arms

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Port.Lag
open Finset Matrix
variable {p : ℕ} {J : Type} [DecidableEq J] [Fintype J]
noncomputable section

def others (u : J → Pinpoint p) (i : J) :=
  (univ.erase i).filter fun j => u j ≠ Option.none
@[simp] theorem active_iff (u : J→Pinpoint p) (i j) :
    j∈others u i ↔ j≠i ∧ u j≠Option.none := by simp [others]

def direct (i : J) (u : J → Pinpoint p) (a : Span p) :=
  width (D i) a :: repeatA i (others u i).toList u
def point (e : J→Pinpoint p) (j : ℕ) : J→Tower p j :=
  fun i => (e i).stamp j

theorem directing (i : J) (u : J→Pinpoint p) (a : Span p) (e : u i=some a) (j)
    (s : Duplex J (Tower p j)) :
    (direct i u a).foldl (fire j) s =
      (s.1,Function.update s.2 i ((point u j) ⬝ᵥ s.2)) := by
  rw [direct,List.foldl_cons, Lag.active i _ (by simp),fire,place,hear]
  have hh :
      (List.map (fun k => (u k).stamp j * Function.update s.2 i (a.land j*s.2 i) k)
        (others u i).toList).sum =
      (∑ k ∈ univ.erase i, (u k).stamp j*s.2 k) := by
    rw [Finset.sum_map_toList,others, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have ne := ne_of_mem_erase hk
    cases hu : u k with
    | none => simp
    | some c => simp [ne]
  have ht := Finset.add_sum_erase (f:=fun k => (u k).stamp j*s.2 k) univ (mem_univ i)
  simp only [ite_true,Function.update_self,dotProduct,point]
  rw [hh, ← ht,e]
  simp [Pinpoint.stamp]

theorem restore (i : J) (u : J→Pinpoint p) (a : Span p) (e : u i=some a)
    (rank : J→ℕ) (leR : ∀ k∈others u i,rank k < rank i)
    (j) (s : J→Tower p j) (x : J→Tower p j) :
    ((direct i u a).reverse.map rewind).foldl (fire j)
      (x,Function.update s i ((point u j) ⬝ᵥ s)) = (x,s) := by
  rw [show (x,Function.update s i ((point u j) ⬝ᵥ s)) =
    (direct i u a).foldl (fire j) (x,s) from (directing i u a e j (x,s)).symm]
  apply backlist j (x,s) _ rank
  intro y h
  rcases List.mem_cons.mp h with eq|q
  · subst y; trivial
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp q
  change early rank (D c) (D i)
  exact Or.inr ⟨rfl,leR c (by simpa using hc)⟩

def slope (down : Bool) (a : Span p) (v : Pinpoint p) :=
  let z := v.right a.reciprocal
  if down then Pinpoint.opposite z else z

def throwUp (i : J) (u : J→Pinpoint p) (a : Span p) (d : Bool) :=
  wave i (others u i).toList (fun k => slope d a (u k))

theorem throwing (i : J) (u : J→Pinpoint p) (a : Span p) (d : Bool)
    (j) (s : Duplex J (Tower p j)) :
    (throwUp i u a d).foldl (fire j) s = ((fun k => s.1 k +
      if k=i then 0 else
        (if d then (-(u k).stamp j) else (u k).stamp j)*a.reciprocal.land j*s.1 i),s.2) := by
  rw [throwUp,Lag.progress _ _ (by simp) (Finset.nodup_toList _)]
  refine Prod.ext ?_ rfl
  funext k
  change _+_ = _+_
  congr 1
  by_cases he : k=i
  · simp [he]
  simp only [he,ite_false,Finset.mem_toList, active_iff]
  cases t : u k <;> cases d <;> simp [slope,Pinpoint.rscale,he]

/-- full script for one outer product. -/
def shot (k t : J) (u v : J→Pinpoint p) (a b : Span p) :=
  direct t v b ++ throwUp k u a true ++ peak k t a ++ throwUp k u a false ++
    (direct t v b).reverse.map rewind

theorem strikes (k t : J) (u v : J→Pinpoint p) (a b : Span p)
    (ha : u k=some a) (hb : v t=some b)
    (rank : J→ℕ) (hv : ∀ l∈others v t,rank l<rank t)
    (j) (s : Duplex J (Tower p j)) :
    (shot k t u v a b).foldl (fire j) s =
      (s.1 + fun i => point u j i*((point v j) ⬝ᵥ s.2), s.2) := by
  simp only [shot,List.foldl_append]
  rw [directing t v b hb,throwing,middle,throwing]
  rw [restore t v b hb rank hv]
  let B := point v j ⬝ᵥ s.2
  refine Prod.ext ?_ rfl
  funext l
  by_cases el : l=k
  · subst l
    simp [point,ha,Pinpoint.stamp]
  simp only [Function.update_of_ne el, el, ite_false,
    ite_true, Bool.false_eq_true, Function.update_self, Pi.add_apply,add_zero,point]
  have g := a.land_rec (j:=j)
  linear_combination (((v |> fun _ => u) l).stamp j * ((point v j ⬝ᵥ s.2))) * g

theorem passes (k t : J) (u v : J→Pinpoint p) (a b : Span p) (rank : J→ℕ)
    (hu : ∀ j∈others u k,rank k<rank j)
    (hv : ∀ l∈others v t,rank l<rank t) :
    (∀ r ∈ shot k t u v a b,r.legal rank) ∧
      ((shot k t u v a b).map prices).sum=1 := by
  constructor
  · have hh (d : Bool) (x) (e : x∈throwUp k u a d) : x.legal rank := by
      obtain ⟨w,y,rfl⟩ := List.mem_map.mp e
      exact Or.inr ⟨rfl,hu _ (by simpa using y)⟩
    have ht (x) (e : x∈direct t v b) : x.legal rank := by
      rcases List.mem_cons.mp e with f|g
      · subst x; trivial
      obtain ⟨w,y,rfl⟩ := List.mem_map.mp g
      exact Or.inr ⟨rfl,hv _ (by simpa using y)⟩
    intro x e
    simp only [shot,List.mem_append,List.mem_map,List.mem_reverse] at e
    rcases e with (((h|h)|h)|h)|⟨l,h,rfl⟩
    · exact ht x h
    · exact hh true x h
    · exact peakLegal rank k t a x h
    · exact hh false x h
    exact rewind_legal _ _ (ht l h)
  simp [shot,direct,repeatA,peak,throwUp,wave,prices,Function.comp_def,List.map_reverse,rewind]
end
end Port.Lag

end IntegerMultiplication
end Computability
end OAI
