import OAI.Computability.NearSquareRoot.InterchangeROMColorBatch
import OAI.Computability.NearSquareRoot.InterchangeROMAddressLanes
import OAI.Computability.NearSquareRoot.InterchangeCalls

/-! # Stable class routing for a variable-radix leaf interchange -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMLeaf

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Loom
  IntegerMultiplication.Adic NearSquareRoot.InterchangeAddress
  NearSquareRoot.InterchangeROMAddress

private theorem select_aux {A V : Type} [DecidableEq A] (a : A) (v : A → List V)
    (l : List A) (nd : l.Nodup) :
    (l.map fun z => if z=a then v z else []).flatten = if a ∈ l then v a else [] := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨nx,rest⟩ := List.nodup_cons.mp nd
    by_cases eq : x = a
    · subst x
      simp [ih rest,nx]
    · have ne : a ≠ x := Ne.symm eq
      simp [eq,ne,ih rest]

private theorem select {A V : Type} [DecidableEq A] (s : Series A) (a : A) (v : A → List V) :
    (s.tab fun z => if z=a then v z else []).flatten = v a := by
  simpa only [Series.tab,s.complete a,ite_true] using select_aux a v s.explore s.nodup

private theorem uniform {A V : Type} (s : Series A) (tag k : ℕ) (f : A → V) :
    Ribbon.read k (s.tab fun x => (tag,f x)) = if tag=k then s.tab f else [] := by
  by_cases e : tag=k <;> simp [Ribbon.read,Ribbon.keep,Series.tab,List.map_map,Function.comp_def,e]
  induction s.explore with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem one_lane {P A G B V : Type} (p : Series P) (d : Series A) (g : Series G)
    (b : Series B) (tag : A → A → ℕ) (k : ℕ) (u w : A)
    (hk : ∀ x y, tag x y = k ↔ x = u ∧ y = w)
    (v : P × A × G × A × B → V) :
    Ribbon.read k ((p.cart (d.cart (g.cart (d.cart b)))).tab
      fun x => (tag x.2.1 x.2.2.2.1,v x)) =
      (p.tab fun i => (g.tab fun j => b.tab fun t => v (i,u,j,w,t)).flatten).flatten := by
  classical
  have bottom (i : P) (x : A) (j : G) :
      Ribbon.read k ((d.cart b).tab fun y => (tag x y.1,v (i,x,j,y))) =
        if x=u then b.tab (fun t => v (i,u,j,w,t)) else [] := by
    rw [read_product]
    simp_rw [uniform,hk]
    by_cases hit : x = u
    · subst x
      simp only [true_and,ite_true]
      exact select d w _
    · simp [hit,Series.tab]
  have mid (i : P) (x : A) :
      Ribbon.read k ((g.cart (d.cart b)).tab
        fun z => (tag x z.2.1,v (i,x,z))) =
          if x=u then (g.tab fun j => b.tab fun t => v (i,u,j,w,t)).flatten else [] := by
    rw [read_product]
    simp_rw [bottom]
    by_cases hit : x=u <;> simp [hit,Series.tab]
  rw [read_product]
  congr 1
  apply congrArg (p.tab)
  funext i
  rw [read_product]
  simp_rw [mid]
  exact select d u _

private theorem no_lane {A V : Type} (s : Series A) (tag : A → ℕ) (val : A → V)
    (k : ℕ) (miss : ∀ a, tag a ≠ k) : Ribbon.read k (s.tab fun a => (tag a,val a)) = [] := by
  simp [Ribbon.read,Ribbon.keep,Series.tab,List.map_map,Function.comp_def,miss]

noncomputable def color {A : Type} (d : Series A) (x y : A) : ℕ :=
  Nat.pair (d.index x).val (d.index y).val

private theorem color_inj {A : Type} (d : Series A) (x y u v : A) :
    color d x y = color d u v ↔ x=u ∧ y=v := by
  simp [color,Nat.pair_eq_pair,Fin.val_eq_val]

/-- Source labels use the two field ranks in their original order. After the
swap the labels occur in the opposite order, and every class retains its
complete prefix, gap and suffix sequence. -/
noncomputable def rows {b : ℕ} (a : Request b) : InterchangeROMColors.Rows where
  source := a.rows.tab fun z => (color (line b a.width) z.2.1 z.2.2.2.1,a.contents z)
  target := a.rows.tab fun z => (color (line b a.width) z.2.2.2.1 z.2.1,
    a.contents (swapper _ _ _ z))
  lengths := by simp
  lanes k := by
    let d := line b a.width
    by_cases known : ∃ u v, color d u v = k
    · obtain ⟨u,v,eq⟩ := known
      subst k
      have f := one_lane (layout a.before) d (layout a.between) (layout a.after_)
        (color d) (color d u v) u v (fun x y => color_inj d x y u v) a.contents
      have g := one_lane (layout a.before) d (layout a.between) (layout a.after_)
        (fun x y => color d y x) (color d u v) v u
        (fun x y => (color_inj d y x u v).trans and_comm)
        (a.contents ∘ swapper _ _ _)
      exact f.trans g.symm
    · exact (no_lane a.rows _ a.contents k (fun x h => known ⟨x.2.1,x.2.2.2.1,h⟩)).trans
        (no_lane a.rows _ (a.contents ∘ swapper _ _ _) k
          (fun x h => known ⟨x.2.2.2.1,x.2.1,h⟩)).symm

abbrev ranks (D : ℕ) := (Series.natural D).cart (Series.natural D)

def label {D : ℕ} (p : Fin D × Fin D) := Nat.pair p.1 p.2

private theorem label_injective (D : ℕ) : Function.Injective (label (D:=D)) := by
  intro x y h
  obtain ⟨hu,hv⟩ := Nat.pair_eq_pair.mp h
  exact Prod.ext (Fin.ext hu) (Fin.ext hv)

/-- The complete ordinal class catalog in row-major order. -/
noncomputable def batch {b : ℕ} (a : Request b) : InterchangeROMColors.Batch where
  toRows := rows a
  colors := (ranks (line b a.width).count).tab label
  distinct := (ranks _).nodup.map (label_injective _)
  covers := by
    rintro z hz
    obtain ⟨x,rfl⟩ := (a.rows.elements _ z).mp hz
    exact ((ranks _).elements _ _).mpr
      ⟨((line b a.width).index x.2.2.2.1,(line b a.width).index x.2.1),rfl⟩

/-- Boolean source and destination masks for one catalog entry. -/
noncomputable def masks {b : ℕ} (a : Request b)
    (p : Fin (line b a.width).count × Fin (line b a.width).count) : List Bool × List Bool :=
  let d := line b a.width
  (a.rows.tab fun z => decide (d.index z.2.1 = p.1 ∧ d.index z.2.2.2.1 = p.2),
   a.rows.tab fun z => decide (d.index z.2.1 = p.2 ∧ d.index z.2.2.2.1 = p.1))

theorem masks_eq {b : ℕ} (a : Request b) (p) : (batch a).masks (label p) = masks a p := by
  simp only [InterchangeROMColors.Rows.masks,InterchangeROMColors.taggedMask,batch,rows,
    masks,color,label,Series.tab,List.map_map,Function.comp_def,Nat.pair_eq_pair,Fin.val_eq_val,and_comm]

theorem bank_eq {b : ℕ} (a : Request b) :
    ((batch a).colors.map (batch a).masks) = (ranks _).tab (masks a) := by
  change ((ranks _).tab label).map _ = _
  rw [Series.map_tab]
  exact congrArg ((ranks _).tab) (funext fun p => masks_eq a p)

@[simp] theorem original {b : ℕ} (a : Request b) :
    send (batch a).values = stripe a.rows a.contents := by
  simp [batch,InterchangeROMColors.Rows.values,rows,Series.tab,Function.comp_def]

@[simp] theorem permuted {b : ℕ} (a : Request b) :
    send (batch a).answer = (Request.job b).reply a := by
  change _ = stripe a.rows (a.contents ∘ swapper _ _ _)
  simp [batch,InterchangeROMColors.Rows.answer,rows,Series.tab,Function.comp_def]

end InterchangeROMLeaf

end NearSquareRoot
end Computability
end OAI
