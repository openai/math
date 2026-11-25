import OAI.Computability.IntegerMultiplication.Net.Boxes

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Motif.Halo
open Finset Matrix Tensor Plate
variable {T J : Type} [DecidableEq T] [DecidableEq J] [Fintype J]

abbrev crowd (idx : S → T → J) (j : S) (p : Sub T) :=
  tile idx (wide j p) \ tile idx (minus j p)
variable (idx : S → T → J)
def canvas : Place T → Finset (S → J)
| .opening a => grain idx a
| .box n a => tile idx (tail n a)
| .ybox n a => tile idx (tail n a) \ grain idx a
| .low j p => crowd idx j p
| .leanOn j p t => crowd idx j p ∪ grain idx (fill j p t)
| .high j p => tile idx (wide j p)
| .full => univ
| .clear => ∅

omit [DecidableEq T] in
theorem clean (j : S) (p : Sub T) (t : T) :
    Disjoint (crowd idx j p) (grain idx (fill j p t)) := by
  refine Finset.disjoint_left.mpr (fun x hx ht => ?_)
  exact (mem_sdiff.mp hx).2 (grain_slab idx j p t ht)

def limit : Place T → Prop
| .box n _ => n≤3
| .ybox n _ => n≤3
| _ => True

-- identify size exactly
omit [DecidableEq T] in
theorem eval (l : Place T) (li : limit l) :
    ((canvas idx l).card : ℤ) = Place.charge (Fintype.card J) l := by
  have g (a : Keys T) : (grain idx a).card = 1 := by
    simp [grain, area_tail idx 0 a (by decide)]
  have e (j : S) : j.val+1 ≤ 3 := by omega
  have y (j : S) (p : Sub T) :
      ((crowd idx j p).card : ℤ) =
        (Fintype.card J : ℤ)^(j.val+1) - (Fintype.card J) := by
    rw [card_sdiff_of_subset (minus_in idx j p),
      Nat.cast_sub (card_le_card (minus_in idx j p)), area_minus, wide, area_tail _ _ _ (e j),
      Nat.cast_pow]
  cases l with
  | opening a => rw [canvas, g, Place.charge]; simp
  | box n a => rw [canvas,area_tail _ _ _ li, Place.charge]; simp
  | ybox n a =>
    rw [canvas, card_sdiff_of_subset (grain_in idx n a),
      Nat.cast_sub (card_le_card (grain_in idx n a)), g, area_tail _ _ _ li, Place.charge]
    simp
  | high j p => rw [canvas, wide, area_tail _ _ _ (e j), Place.charge]; simp
  | low j p => exact y j p
  | leanOn j p t =>
    rw [canvas, card_union_of_disjoint (clean idx j p t), Nat.cast_add, g, y, Place.charge]
    simp
  | full => simp [canvas, Place.charge, S]
  | clear => simp [canvas, Place.charge]

variable {R : Type} [CommRing R]
variable (P : T → Mat J R)
-- projection formula at tail pins
abbrev proj (n : ℕ) (a : Keys T) : Mat (S→J) R := cube P (tail n a)
abbrev upper (j : S) (p : Sub T) := cube P (wide j p) - cube P (minus j p)

def operator : Place T → Mat (S → J) R
| .opening a => proj P 0 a
| .box n a => proj P n a
| .ybox n a => proj P n a - proj P 0 a
| .low j p => upper P j p
| .leanOn j p t => upper P j p + proj P 0 (fill j p t)
| .high j p => cube P (wide j p)
| .full => 1
| .clear => 0

omit [DecidableEq T] [Fintype J] in
@[simp] theorem finalForm (a : Keys T) : proj P 3 a = 1 := by
  unfold proj cube
  simp_rw [tail_none]
  exact Tensor.unit
omit [DecidableEq T] [Fintype J] in
@[simp] theorem finalForm' (p : Keys T) : operator P (.box 3 p) = 1 := finalForm P p
omit [DecidableEq T] [Fintype J] in
@[simp] theorem finalForm'' (p : Keys T) : operator P (.ybox 3 p) = 1-proj P 0 p := by
  rw [operator, finalForm]

/-- When P is honored by Z on contributing tensor positions, the place operator is a slice. -/
def material (Z : S → Chart J R) (l : Place T) :=
  operator P l = (weave Z).slice (shade R (canvas idx l))

variable (Z : S → Chart J R)
def grant (A : Keys T) := ∀ i, P (A i) = (Z i).ray (idx i (A i))

omit [DecidableEq T] in
theorem ray_tail (a : Keys T) (n : ℕ) (g : grant idx P Z a) :
    cube P (tail n a) = (weave Z).slice (shade R (tile idx (tail n a))) := by
  apply model
  intro i b e
  simp [tail] at e
  rw [← e.2]; exact g i

omit [DecidableEq T] in
theorem entry (j : S) (a : Keys T) (g : grant idx P Z a) :
    material idx P Z (Place.xEntry j.val a) ∧
      canvas idx (Place.xEntry j.val a) = tile idx (tail j.val a) := by
  by_cases q : j.val=0
  · rw [Place.xEntry, ite_eq_left q, q]
    exact ⟨ray_tail idx P Z a 0 g,rfl⟩
  simp only [Place.xEntry, ite_eq_right q, material, operator, canvas, proj,
    ray_tail idx P Z a _ g, true_and]

omit [DecidableEq T] in
theorem box (a : Keys T) (n : ℕ) (g : grant idx P Z a) :
    material idx P Z (.box n a) := ray_tail idx P Z a n g
omit [DecidableEq T] in
theorem ybox (a : Keys T) (n : ℕ) (g : grant idx P Z a) :
    material idx P Z (.ybox n a) := by
  rw [material,canvas,operator, Plate.sdiff _ _ (grain_in idx n a),
    Chart.slice_sub, proj, proj, grain, ray_tail idx P Z a n g, ray_tail idx P Z a 0 g]
omit [DecidableEq T] in
theorem commonl (j : S) (p : Sub T) (t : T)
    (g : grant idx P Z (fill j p t)) : material idx P Z (.high j p) ∧ material idx P Z (.low j p) := by
  have a : material idx P Z (.high j p) := by
    rw [material,canvas,operator,wide_acts j p t, ray_tail idx P Z _ _ g]
  refine ⟨a,?_⟩
  unfold material at *
  rw [operator,canvas] at a
  rw [operator,canvas,crowd,Plate.sdiff _ _ (minus_in idx j p), Chart.slice_sub,
    upper, a]
  rw [model (minus j p)]
  intro i b e
  simp [minus] at e
  obtain ⟨hi, ho⟩ := e
  rw [← ho, fill_other j p (p 0) t hi]
  exact g i
omit [DecidableEq T] in
theorem support (j : S) (p : Sub T) (t : T)
    (g : grant idx P Z (fill j p t)) : material idx P Z (.leanOn j p t) := by
  have s := (commonl idx P Z j p t g).2
  rw [material,operator,canvas,Plate.disjsum (R:=R) _ _ (clean idx j p t), Chart.slice_add,
    proj, grain, ray_tail idx P Z _ _ g]
  unfold material at s; rw [operator, canvas] at s; rw [s]
omit [DecidableEq T] in
theorem empty : material idx P Z .clear := by
  rw [material, operator, canvas, show shade R (∅ : Finset (S → J))=0 by ext; simp [Plate.shade], Chart.slice_zero]
omit [DecidableEq T] in
theorem saturated : material idx P Z .full := by
  rw [material, operator, canvas, show shade R (univ : Finset (S → J))=(fun _ => 1) by ext; simp [Plate.shade], Chart.slice_unit]
end Net.Motif.Halo

end IntegerMultiplication
end Computability
end OAI
