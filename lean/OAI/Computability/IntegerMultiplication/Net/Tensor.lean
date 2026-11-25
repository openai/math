import Mathlib

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Tensor
open Finset Matrix
variable {I J R : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable [CommRing R]
abbrev Mat J R := Matrix J J R
abbrev Vec J R := J → R

/-- entrywise tensor product -/
def mat (a : I → Mat J R) : Mat (I → J) R := Matrix.of
  (fun x y => ∏ i, a i (x i) (y i))
def vec (a : I → Vec J R) : Vec (I → J) R := fun x => ∏ i, a i (x i)
omit [Fintype J] [DecidableEq I] [DecidableEq J] in
@[simp] theorem app (a : I → Mat J R) (x y : I → J) :
    mat a x y = ∏ i, a i (x i) (y i) := rfl

omit [DecidableEq J] in
theorem multiply (a b : I → Mat J R) :
    mat a * mat b = mat (fun i => a i * b i) := by
  ext x y
  simp_rw [app, Matrix.mul_apply, app, ← Finset.prod_mul_distrib, Fintype.prod_sum]

omit [DecidableEq I] in
theorem prod_indicator (p : I → Prop) [DecidablePred p] :
    ∏ i, (if p i then (1:R) else 0) = if ∀ i, p i then 1 else 0 := by
  classical
  by_cases h : ∀ i, p i
  · simp [h]
  have : ∃ i, ¬p i := not_forall.mp h
  obtain ⟨i, hi⟩ := this
  rw [Finset.prod_eq_zero (Finset.mem_univ i)]
  · simp [h]
  simp [hi]

omit [Fintype J] in
omit [DecidableEq I] in
theorem unit : mat (fun _ : I => (1 : Mat J R)) = 1 := by
  ext x y
  simp_rw [app, Matrix.one_apply, prod_indicator (R:=R),
    show (∀ i, x i = y i) ↔ x = y from funext_iff.symm]

omit [Fintype J] [DecidableEq I] in
theorem diag (a : I → Vec J R) :
    mat (fun i => Matrix.diagonal (a i)) = Matrix.diagonal (vec a) := by
  ext x y
  classical
  by_cases h : x = y
  · subst y; simp [app, vec]
  rw [Matrix.diagonal_apply_ne _ h, app]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := not_forall.mp (fun h' => h (funext h'))
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (Matrix.diagonal_apply_ne _ hi)

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem flip (a : I → Mat J R) : (mat a).transpose = mat (fun i => (a i).transpose) := rfl

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem outer (a b : I → Vec J R) :
    mat (fun i => vecMulVec (a i) (b i)) = vecMulVec (vec a) (vec b) := by
  ext x y
  simp [vec, app, vecMulVec_apply, Finset.prod_mul_distrib]

/-- reversible coordinate matrix -/
structure Chart (J R : Type) [Fintype J] [DecidableEq J] [CommRing R] where
  push : Mat J R
  pull : Mat J R
  rev : pull * push = 1
  rev' : push * pull = 1

def weave (Z : I → Chart J R) : Chart (I → J) R where
  push := mat (fun i => (Z i).push)
  pull := mat (fun i => (Z i).pull)
  rev := by rw [multiply]; simpa only [Chart.rev] using unit (I:=I) (J:=J) (R:=R) -- fails simpa direction?
  rev' := by rw [multiply]; simpa only [Chart.rev'] using unit (I:=I) (J:=J) (R:=R)

namespace Chart
variable (z : Chart J R)
/-- operator diagonal in this chart (projection when d labels 0/1). -/
def slice (d : Vec J R) := z.push * Matrix.diagonal d * z.pull
def primal (i : J) : Vec J R := fun u => z.push u i
def dual (i : J) : Vec J R := fun u => z.pull i u
def ray (i : J) : Mat J R := vecMulVec (z.primal i) (z.dual i)

theorem sum_rays (d : Vec J R) :
    z.slice d = ∑ i, d i • z.ray i := by
  ext x y
  simp [slice, Matrix.mul_apply, Matrix.diagonal_apply, ray, primal, dual, vecMulVec_apply,
    Matrix.sum_apply]
  apply sum_congr rfl
  intros; ring

@[simp] theorem slice_zero : z.slice 0 = 0 := by simp [sum_rays]
@[simp] theorem slice_unit : z.slice (fun _ => 1) = 1 := by
  simp [slice, z.rev']
theorem slice_add (d e : Vec J R) : z.slice (d+e)= z.slice d + z.slice e := by
  simp [sum_rays, add_smul, Finset.sum_add_distrib]
theorem slice_sub (d e : Vec J R) : z.slice (d-e)= z.slice d - z.slice e := by
  simp [sum_rays, sub_smul, Finset.sum_sub_distrib]

theorem slice_one_at (k : J) : z.slice (fun i => if i=k then 1 else 0)= z.ray k := by
  rw [sum_rays, Finset.sum_eq_single k] <;> aesop

end Chart
theorem slice (Z : I → Chart J R) (d : I → Vec J R) :
    (weave Z).slice (vec d) = mat (fun i => (Z i).slice (d i)) := by
  simp only [weave, Chart.slice, ← diag d, multiply]
end Net.Tensor

end IntegerMultiplication
end Computability
end OAI
