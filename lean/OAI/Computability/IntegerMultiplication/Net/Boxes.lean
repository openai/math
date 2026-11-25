import OAI.Computability.IntegerMultiplication.Net.Picture
import OAI.Computability.IntegerMultiplication.Net.Labels

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Motif
open Finset Matrix Tensor Plate
namespace Halo
variable {T : Type}

def tail (n : ℕ) (a : Keys T) : Spec S T :=
  fun k => if n ≤ k.val then some (a k) else none
def minus (j : S) (p : Sub T) : Spec S T :=
  fun k => if k=j then none else some (fill j p (p 0) k)

def wide (j : S) (p : Sub T) : Spec S T :=
  tail (j.val+1) (fill j p (p 0))
theorem wide_acts (j : S) (p : Sub T) (t : T) :
    wide j p = tail (j.val+1) (fill j p t) := by
  funext k
  unfold wide tail
  split_ifs with h
  · have hj : k ≠ j := by intro e; subst k; omega
    rw [fill_other j p _ t hj]
  rfl
@[simp] theorem tail_none (a : Keys T) (k : S) : tail 3 a k = none := by
  unfold tail; have : k.val < 3 := k.isLt; simp [Nat.not_le_of_lt this]

variable {J : Type} [DecidableEq J] [Fintype J] [DecidableEq T]
def grain (idx : S → T → J) (a : Keys T) := tile idx (tail 0 a)
omit [DecidableEq J] [DecidableEq T] in
theorem grain_in (idx : S → T → J) (n : ℕ) (a : Keys T) : grain idx a ⊆ tile idx (tail n a) := by
  apply encloses
  intro i t e
  unfold tail at *
  simp only [Nat.zero_le, ite_true]
  split at e <;> simp_all
omit [DecidableEq J] [DecidableEq T] in
theorem minus_in (idx : S → T → J) (j : S) (p : Sub T) :
    tile idx (minus j p) ⊆ tile idx (wide j p) := by
  apply encloses
  intro i t e
  unfold wide tail at e
  split_ifs at e with hn
  · have ne : i ≠ j := by rintro rfl; omega
    simpa [minus, ne] using e
omit [DecidableEq J] [DecidableEq T] in
theorem grain_slab (idx : S → T → J) (j : S) (p : Sub T) (u : T) :
    grain idx (fill j p u) ⊆ tile idx (minus j p) := by
  apply encloses
  intro i t e
  by_cases ne : i=j
  · simp [minus, ne] at e
  simpa [tail, fill_other j p u (p 0) ne] using (by simpa [minus, ne] using e : fill j p (p 0) i = t)
omit [DecidableEq J] [DecidableEq T] in
theorem end_in (idx : S → T → J) (j : S) (p : Sub T) (t : T) :
    tile idx (tail j.val (fill j p t)) ⊆ tile idx (wide j p) := by
  rw [wide_acts _ _ t]
  apply encloses
  intro k u e
  unfold tail at e ⊢
  have : j.val+1 ≤ k.val := by
    by_contra h
    simp [h] at e
  simpa [this, show j.val ≤ k.val by omega] using e

omit [DecidableEq T] in
theorem overlap (idx : S → T → J) (j : S) (p : Sub T) (t : T) :
    tile idx (tail j.val (fill j p t)) ∩ tile idx (minus j p) =
      grain idx (fill j p t) := by
  apply Subset.antisymm
  · intro x e
    rw [mem_inter, inside, inside] at e
    rw [grain, inside]
    intro k r h
    have he : fill j p t k = r := by simpa [tail] using h
    by_cases hj : k=j
    · subst k
      exact e.1 j r (by simpa [tail] using he)
    apply e.2 k r
    simp only [minus, ite_eq_right hj, Option.some.injEq]
    rwa [fill_other j p (p 0) t hj]
  exact subset_inter (grain_in ..) (grain_slab ..)

omit [DecidableEq J] [DecidableEq T] in
theorem apart (idx : S → T → J) (j : S) (p : Sub T) (t u : T)
    (diff : idx j t ≠ idx j u) :
    Disjoint (grain idx (fill j p t)) (grain idx (fill j p u)) := by
  apply Finset.disjoint_left.mpr
  intro x a b
  apply diff
  rw [grain, inside] at a b
  have at0 := a j t (by simp [tail])
  have bt0 := b j u (by simp [tail])
  rw [← at0, bt0]
omit [DecidableEq J] [DecidableEq T] in
theorem area_tail (idx : S → T → J) (n : ℕ) (a : Keys T) (h : n≤3) :
    (tile idx (tail n a)).card = (Fintype.card J)^n := by
  rw [area, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  interval_cases n <;> norm_num [tail,S] <;> ring
omit [DecidableEq J] [DecidableEq T] in
theorem area_minus (idx : S → T → J) (j : S) (p : Sub T) :
    (tile idx (minus j p)).card = (Fintype.card J) := by
  rw [area, Finset.prod_eq_single j]
  · simp [minus]
  · intro i _ e; simp [minus,e]
  simp

end Halo
end Net.Motif

end IntegerMultiplication
end Computability
end OAI
