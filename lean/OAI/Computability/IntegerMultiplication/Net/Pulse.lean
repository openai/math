import OAI.Computability.IntegerMultiplication.Net.Tensor

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Tensor
open Finset Matrix
namespace Kick
variable {J R : Type} [Fintype J] [DecidableEq J] [CommRing R]
variable (P : Finset J) (v : J → Vec J R)
-- supported orthonormal vectors (no component on P), in char 2
def direction (i : J) : Vec J R := v i + Pi.single i 1
def extend (i : J) : Vec J R :=
  Pi.single i 1 + ∑ j ∈ P, direction v j i • direction v j
variable (z2 : ∀ a : R, a+a=0)
variable (hs : ∀ i ∈ P, ∀ j ∈ P, v j i = 0)
variable (ho : ∀ i ∈ P, ∀ j ∈ P, v i ⬝ᵥ v j = if i=j then 1 else 0)

include z2 hs ho in
theorem annul (i j : J) (hi : i∈P) (hj : j∈P) :
    direction v i ⬝ᵥ direction v j = 0 := by
  by_cases e : i=j
  · subst j
    simp [direction, add_dotProduct, dotProduct_add, ho _ hi _ hi,
      hs _ hi _ hi, z2]
  simp [direction, add_dotProduct, dotProduct_add, ho _ hi _ hj, e,
    hs _ hi _ hj, hs _ hj _ hi, Ne.symm e]

include z2 hs in
omit [Fintype J] in
theorem pinned (i : J) (hi : i∈P) : extend P v i = v i := by
  rw [extend, Finset.sum_eq_single_of_mem _ hi]
  · simp only [direction, Pi.add_apply, hs _ hi _ hi, Pi.single_eq_same, zero_add, one_smul]
    have : Pi.single i (1:R) + (Pi.single i 1 : Vec J R) = 0 := by
      funext; exact z2 _
    rw [add_left_comm, this, add_zero] -- needed
  intro b hb e
  simp [direction, hs _ hi _ hb, Ne.symm e]

include z2 hs ho in
theorem kick_dot (i j : J) :
    extend P v i ⬝ᵥ extend P v j = if i=j then 1 else 0 := by
  simp only [extend, add_dotProduct, dotProduct_add, dotProduct_single_one,
    single_one_dotProduct, sum_dotProduct, dotProduct_sum]
  simp_rw [smul_dotProduct, dotProduct_smul]
  -- simplify
  rw [Finset.sum_congr rfl (g:=fun x => (direction v x j • direction v x) i) (s₁:=P) (by
    intro k hk
    rw [Finset.sum_eq_zero]
    · rw [add_zero]
    intro l hl
    rw [annul P v z2 hs ho l k hl hk, smul_zero, smul_zero])] -- parameter s₁?
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_assoc]
  have eq : ∑ x ∈ P, direction v x j * direction v x i =
      ∑ x ∈ P, direction v x i * direction v x j := sum_congr rfl (by intros; rw [mul_comm])
  rw [eq, z2, add_zero]
  simp [Pi.single_apply, eq_comm]
def mint (P : Finset J) (v : J → Vec J R)
    (z2 : ∀ a : R, a+a=0)
    (hs : ∀ i ∈ P, ∀ j ∈ P, v j i = 0)
    (ho : ∀ i ∈ P, ∀ j ∈ P, v i ⬝ᵥ v j = if i=j then 1 else 0) :
    Chart J R :=
  let H : Mat J R := Matrix.of fun i j => extend P v j i
  have Z : H.transpose * H = 1 := by
    ext i j
    simpa [H, Matrix.mul_apply, Matrix.one_apply, dotProduct] using kick_dot P v z2 hs ho i j
  ⟨H,H.transpose,Z,mul_eq_one_comm.mp Z⟩

@[simp] theorem orthog (z2 hs ho) : (mint P v z2 hs ho).pull =
    (mint P v z2 hs ho).push.transpose := rfl
@[simp] theorem pins (z2 hs ho i) (hi : i∈P) :
    (mint P v z2 hs ho).ray i = vecMulVec (v i) (v i) := by
  ext k j
  simp [mint, Chart.ray, Chart.primal, Chart.dual, vecMulVec_apply, pinned P v z2 hs i hi]
end Kick
end Net.Tensor

end IntegerMultiplication
end Computability
end OAI
