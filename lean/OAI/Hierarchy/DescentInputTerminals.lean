import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic

namespace OAI
/-! # Assigning each old tensor in a leaf to a single rotor input -/

namespace Hierarchy.DescentBaseProfile
open scoped BigOperators Classical
noncomputable section
variable {I : Type*} {Y : ℕ}

def inputLoad (S : Finset I) (wt : I → ℝ) (atRow : I → Fin Y) (j : Fin Y) : ℝ :=
  ∑i∈S,if atRow i=j then wt i else 0

/-- Greedy minimum-load placement. All ports of an old occurrence use its
single assigned row. The range of the row loads never exceeds one item. -/
theorem least_loaded [NeZero Y] (wt : I → ℝ) {B : ℝ} (posB : 0≤B)
    (pos : ∀i,0≤wt i) (bound : ∀i,wt i≤B) (S : Finset I) :
    ∃ atRow : I → Fin Y, ∀j k,inputLoad S wt atRow j ≤ inputLoad S wt atRow k+B := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _=>0,fun _ _=>by simpa [inputLoad] using posB⟩
  | @insert i S fresh ih =>
    obtain ⟨old,range⟩ := ih
    obtain ⟨best,_,light⟩ := Finset.exists_min_image Finset.univ (inputLoad S wt old) Finset.univ_nonempty
    let next := Function.update old i best
    have loadEq (j : Fin Y) : inputLoad (insert i S) wt next j =
        (if best=j then wt i else 0)+inputLoad S wt old j := by
      unfold inputLoad
      rw [Finset.sum_insert fresh]
      simp only [next,Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun z hz => by
        exact congrArg (fun row : Fin Y => if row=j then wt z else 0) (Function.update_of_ne (show z≠i from fun h => fresh (h ▸ hz)) best old)
    refine ⟨next,fun j k => ?_⟩
    rw [loadEq,loadEq]
    by_cases a : best=j <;> by_cases b : best=k
    · simp only [ite_eq_left a,ite_eq_left b]
      linarith [range j k]
    · subst j
      simp only [ite_true,ite_eq_right b,zero_add]
      linarith [light k (Finset.mem_univ _),bound i]
    · simp only [ite_eq_right a,zero_add,ite_eq_left b]
      linarith [pos i,range j k]
    · simpa [a,b] using range j k

theorem sum_input [Fintype I] (wt : I → ℝ) (atRow : I → Fin Y) :
    (∑j,inputLoad Finset.univ wt atRow j)=∑ i,wt i := by
  unfold inputLoad
  rw [Finset.sum_comm]
  simp

/-- The size bound on a populated leaf gives the advertised load of each
actual assigned input row, before and after absorbing the indivisible item. -/
theorem input_rows [Fintype I] [NeZero Y] (wt : I → ℝ) {B S : ℝ} (posB : 0≤B)
    (pos : ∀i,0≤wt i) (bound : ∀i,wt i≤B) (total : ∑i,wt i≤2*S) (scale : Y*B≤S) :
    ∃ atRow : I → Fin Y, ∀j,inputLoad Finset.univ wt atRow j≤3*S/Y := by
  obtain ⟨atRow,range⟩ := least_loaded (Y:=Y) wt posB pos bound Finset.univ
  refine ⟨atRow,fun j=>?_⟩
  have avg := Finset.sum_le_sum (s:=Finset.univ) (fun k _=>range j k)
  rw [Finset.sum_add_distrib,sum_input] at avg
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at avg
  apply (le_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Y) : (0:ℝ)<Y)).2
  nlinarith

end
end Hierarchy.DescentBaseProfile

end OAI
