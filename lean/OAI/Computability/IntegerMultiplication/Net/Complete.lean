import OAI.Computability.IntegerMultiplication.Net.Tensor

/-! Explicit completions to a coordinate chart. -/

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Tensor
open Finset Matrix
namespace Notch
variable {J R : Type} [Fintype J] [DecidableEq J] [CommRing R]
variable (P : Finset J) (v w : J → Vec J R)
-- pinned columns have independent pivot rows: v j i = δ(i,j) on P
-- w are specified duals with w dot v=δ(i,j).
def col (j : J) : Vec J R :=
  if j∈P then v j else
    Pi.single j 1 - ∑ i ∈ P, w i j • v i
def line (i : J) : Vec J R :=
  if i∈P then w i else
    Pi.single i 1 - ∑ j ∈ P, v j i • Pi.single j 1

variable (hb : ∀ i ∈ P, ∀ j ∈ P, w i ⬝ᵥ v j = if i=j then 1 else 0)
variable (hp : ∀ i ∈ P, ∀ j ∈ P, v j i = if i=j then 1 else 0)

include hp in
theorem almost (i j : J) (hj : j∈P) :
    (Pi.single i 1 - ∑ k ∈ P, v k i • Pi.single k 1) ⬝ᵥ v j =
      if i∈P then (v j i - v j i) else 0 := by
  rw [sub_dotProduct, sum_dotProduct, single_one_dotProduct,
    Finset.sum_eq_single_of_mem _ hj]
  · rw [smul_dotProduct, single_one_dotProduct, smul_eq_mul, hp _ hj _ hj]
    simp
  intro k hk ne
  rw [smul_dotProduct, single_one_dotProduct, hp _ hk _ hj]
  simp [ne]

include hb hp in
theorem inverse (i j : J) :
    line P v w i ⬝ᵥ col P v w j = if i=j then 1 else 0 := by
  unfold line col
  by_cases hi : i∈P
  · rw [ite_eq_left hi]
    split_ifs with hj he
    · simpa only [ite_eq_left he] using hb _ hi _ hj
    · simpa only [ite_eq_right he] using hb _ hi _ hj
    · subst_vars; contradiction
    rw [dotProduct_sub, dotProduct_single_one, dotProduct_sum,
      Finset.sum_eq_single_of_mem _ hi]
    · rw [dotProduct_smul, smul_eq_mul, hb _ hi _ hi]
      simp
    intro k hk ne
    rw [dotProduct_smul, hb _ hi _ hk]
    simp [Ne.symm ne]
  rw [ite_eq_right hi]
  by_cases hj : j∈P
  · rw [ite_eq_left hj, ite_eq_right (show i ≠ j by rintro rfl; contradiction), almost P v hp _ _ hj]
    simp
  rw [ite_eq_right hj, dotProduct_sub, dotProduct_single_one, dotProduct_sum]
  have hw : ∀ k ∈ P, (Pi.single i 1 - ∑ l ∈ P, v l i • Pi.single l 1) ⬝ᵥ (w k j • v k) = 0 := by
    intro k hk
    rw [dotProduct_smul, almost P v hp i k hk]
    simp
  rw [Finset.sum_eq_zero hw]
  have ht : ∀ k ∈ P, v k i * ((Pi.single k 1 : J → R) j) = 0 := by
    intro k hk
    have : j ≠ k := fun e => hj (e ▸ hk)
    simp [Pi.single_eq_of_ne this]
  by_cases eq : j=i <;>
    simp [Finset.sum_apply, Pi.single_apply, eq, smul_eq_mul]
  · simp [hi]
  simp [hj, Ne.symm eq]

include hb hp in
def mint (P : Finset J) (v w : J → Vec J R)
    (hb : ∀ i ∈ P, ∀ j ∈ P, w i ⬝ᵥ v j = if i=j then 1 else 0)
    (hp : ∀ i ∈ P, ∀ j ∈ P, v j i = if i=j then 1 else 0) :
    Chart J R :=
  let A : Mat J R := Matrix.of fun i j => col P v w j i
  let B : Mat J R := Matrix.of fun i => line P v w i
  have Z : B * A = 1 := by
    ext i j
    simpa [B, A, Matrix.mul_apply, Matrix.one_apply, dotProduct] using inverse P v w hb hp i j
  ⟨A,B,Z,mul_eq_one_comm.mp Z⟩

@[simp] theorem pins (hb hp i) (hi : i∈P) :
    (mint P v w hb hp).ray i = vecMulVec (v i) (w i) := by
  ext k j
  simp [mint, Chart.ray, Chart.primal, Chart.dual, vecMulVec_apply, col, line, hi]
end Notch
end Net.Tensor

end IntegerMultiplication
end Computability
end OAI
