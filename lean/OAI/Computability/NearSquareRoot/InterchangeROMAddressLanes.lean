import OAI.Computability.NearSquareRoot.InterchangeROMAddressCommand

/-! # Stable carry classes on native interchange layouts

Each carry class can be gathered and scattered once on the entire flat
stream. An earlier field controls the choice of permutation, while every
prefix, gap and suffix coordinate retains its value and physical order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Loom
  IntegerMultiplication.Adic
variable {A B C T V W : Type} [DecidableEq T]

private theorem read_append (k : T) (u v : List (T × V)) :
    Ribbon.read k (u ++ v) = Ribbon.read k u ++ Ribbon.read k v := by simp [Ribbon.read]

private theorem read_constant (k t : T) (w : List V) :
    Ribbon.read k (w.map fun z => (t,z)) = if t = k then w else [] := by
  induction w with
  | nil => simp [Ribbon.read]
  | cons a w ih =>
    simp only [List.map_cons,Ribbon.read,List.map_cons,List.flatten_cons] at *
    rw [ih]
    by_cases e : t=k <;> simp [Ribbon.keep,e]

/-- A flattened product of differently labeled blocks is read one block at
a time, preserving their original order. -/
theorem read_product (s : Series A) (t : Series B) (k : T) (v : A × B → T × V) :
    Ribbon.read k ((s.cart t).tab v) =
      (s.tab fun a => Ribbon.read k (t.tab fun b => v (a,b))).flatten := by
  rw [Series.grouped]
  unfold Series.tab
  induction s.explore with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,List.flatten_cons,read_append,ih]

/-- A suffix of arbitrary extent can be carried intact through a monochrome
class. This identity applies also to an empty suffix enumeration. -/
theorem read_suffix (s : Series A) (t : Series B) (key : A → T) (k : T)
    (v : A × B → V) :
    Ribbon.read k (blob (s.cart t) (fun x => key x.1) v) =
      (Ribbon.read k (blob s key (fun a => t.tab fun b => v (a,b)))).flatten := by
  unfold blob
  rw [read_product]
  unfold Series.tab
  induction s.explore with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,List.flatten_cons]
    rw [show t.explore.map (fun b => (key a,v (a,b))) =
      (t.explore.map fun b => v (a,b)).map (fun w => (key a,w)) by simp]
    rw [read_constant, ih]
    by_cases e : key a = k <;> simp [Ribbon.read,Ribbon.keep,e]

theorem suffix_lane {s : Series A} {d : Series C} {key : A → T} {tag : C → T}
    (r : Ranger s d key tag) (t : Series B) (v : A × B → V) (k : T) :
    Ribbon.read k (blob (s.cart t) (fun x => key x.1) v) =
      Ribbon.read k (blob (d.cart t) (fun x => tag x.1) (fun x => v (r.run.symm x.1,x.2))) := by
  rw [read_suffix,read_suffix]
  exact congrArg List.flatten (r.lane (fun a => t.tab fun b => v (a,b)) k)

/-- Lift a matching carry lane through an arbitrary unchanged prefix. -/
theorem prefix_lane (l : Series A) (s : Series B) (d : Series C)
    (f : A × B → T × V) (g : A × C → T × V) (k : T)
    (matchLane : ∀ a, Ribbon.read k (s.tab fun b => f (a,b)) =
      Ribbon.read k (d.tab fun c => g (a,c))) :
    Ribbon.read k ((l.cart s).tab f) = Ribbon.read k ((l.cart d).tab g) := by
  rw [read_product,read_product]
  simp only [matchLane]

variable {p f : ℕ} [NeZero p] {s : Series A} {P G S : Tape}

/-- Pull a field's classification back to flat native records. -/
theorem slot_lanes {T U : Type} [DecidableEq T] {u : Series U} {key tag : U → T}
    (e : Slot s P u S) (r : Ranger u u key tag) (v : A → V) (k : T) :
    Ribbon.read k (blob s (key ∘ e.read) v) =
      Ribbon.read k (blob s (tag ∘ e.read) (v ∘ (e.tune r.run).symm)) := by
  let w := v ∘ e.view.cast.symm
  have main := prefix_lane (layout P) (u.cart (layout S)) (u.cart (layout S))
    (fun x => (key x.2.1,w x)) (fun x => (tag x.2.1,w (x.1,r.run.symm x.2.1,x.2.2)))
    k (fun z => suffix_lane r (layout S) (fun x => w (z,x)) k)
  rw [e.view.route, e.view.route] at main
  simpa [blob,Function.comp_def,w,Slot.read,Slot.tune,Slot.alter] using main

/-- The local permutation and its source and destination labels may depend
on the earlier slot, even if an arbitrary spectator region separates them. -/
theorem axis_lanes {T U W : Type} [DecidableEq T] {u : Series U} {t : Series W}
    {key tag : U → W → T} (e : Axis s P u G t S) (r : ∀ a, Ranger t t (key a) (tag a))
    (v : A → V) (k : T) :
    Ribbon.read k (blob s (fun x => key (e.pair x).1 (e.pair x).2) v) =
      Ribbon.read k (blob s (fun x => tag (e.pair x).1 (e.pair x).2)
        (v ∘ (e.tune (slideOver fun a => (r a).run)).symm)) := by
  let w := v ∘ e.view.cast.symm
  let src (x : Pin P × U × Pin G × W × Pin S) := (key x.2.1 x.2.2.2.1,w x)
  let dst (x : Pin P × U × Pin G × W × Pin S) :=
    (tag x.2.1 x.2.2.2.1,w (x.1,x.2.1,x.2.2.1,(r x.2.1).run.symm x.2.2.2.1,x.2.2.2.2))
  have main : Ribbon.read k ((Path P u G t S).tab src) = Ribbon.read k ((Path P u G t S).tab dst) := by
    apply prefix_lane
    intro z
    apply prefix_lane
    intro i
    apply prefix_lane
    intro g
    exact suffix_lane (r i) (layout S) (fun x => w (z,i,g,x)) k
  rw [e.view.route, e.view.route] at main
  simpa [blob,Function.comp_def,w,src,dst,Axis.pair,Axis.tune,Axis.bridge,slideOver] using main

theorem width_lane (e : Slot s P (line p f) S) (a b : Nug p) (off : Tower p f)
    (v : A → V) (k : Seal a b) :
    Ribbon.read k (blob s (fun x => flag a b off (e.read x)) v) =
      Ribbon.read k (blob s (fun x => flag a b off ((swift a b off).symm (e.read x)))
        (v ∘ (e.tune (swift a b off)).symm)) :=
  slot_lanes e (admiral a b off) v k

theorem gather_lane (e : Axis s P (line p f) G (line p f) S) (a b : Nug p)
    (off : Block p f → Tower p f) (v : A → V) (k : Seal a b) :
    Ribbon.read k (blob s (fun x => flag a b (off (e.pair x).1) (e.pair x).2) v) =
      Ribbon.read k (blob s (fun x => flag a b (off (e.pair x).1)
        ((swift a b (off (e.pair x).1)).symm (e.pair x).2))
        (v ∘ (e.tune (slideOver fun i => swift a b (off i))).symm)) :=
  axis_lanes e (fun i => admiral a b (off i)) v k

/-- The two actual digit transducers agree in every physical carry lane
after the native one-field permutation. -/
theorem width_tags (e : Slot s P (line p f) S) (a b : Nug p) (off : Tower p f)
    (raw : Raw p) (holds : Holds f raw off) (v : A → V) (k : Adic.Seal a b) :
    Ribbon.read k (blob s (fun x => post a b (raw,least (e.read x))) v) =
      Ribbon.read k (blob s (fun x => fetch a b (raw,least (e.read x)))
        (v ∘ (e.tune (swift a b off)).symm)) := by
  have left (x : A) := forward_post a b f raw off holds (e.read x)
  have right (x : A) := back_post a b f raw off holds (e.read x)
  simpa only [left,right,byword] using width_lane e a b off v k

/-- Both digit words for a shear come from their original positions in the
layout. The prefix, gap and suffix can vary with the instance. -/
theorem gather_tags (e : Axis s P (line p f) G (line p f) S) (a b : Nug p)
    (off : Block p f → Tower p f) (raw : Block p f → Raw p)
    (holds : ∀ x, Holds f (raw x) (off x)) (v : A → V) (k : Adic.Seal a b) :
    Ribbon.read k (blob s (fun x => post a b (raw (e.pair x).1,least (e.pair x).2)) v) =
      Ribbon.read k (blob s (fun x => fetch a b (raw (e.pair x).1,least (e.pair x).2))
        (v ∘ (e.tune (slideOver fun i => swift a b (off i))).symm)) := by
  have left (x : A) := forward_post a b f _ _ (holds (e.pair x).1) (e.pair x).2
  have right (x : A) := back_post a b f _ _ (holds (e.pair x).1) (e.pair x).2
  simpa only [left,right,byword] using gather_lane e a b off v k

end InterchangeROMAddress

end NearSquareRoot
end Computability
end OAI
