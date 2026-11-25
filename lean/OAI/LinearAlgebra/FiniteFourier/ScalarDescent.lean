import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic

/-! # Restriction of scalars and independent inputs

Expanding every coordinate of an extension-field matrix in a basis over the
ground field gives its base-field action on a block of inputs. If the final
matrix is defined over the ground field, these blocks separate into independent
copies of exactly the same transform.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped BigOperators

noncomputable section

variable {K E : Type*} [CommRing K] [CommRing E] [Algebra K E]
variable {D I J H : Type*} [Fintype D]

/-- Pack a block of ground-field input arrays using a basis of the extension. -/
def packInputs (b : Module.Basis D K E) (x : I × D → K) (i : I) : E :=
  ∑ d, x (i, d) • b d

/-- Unpack the extension array by taking every basis coefficient. -/
def unpackOutputs (b : Module.Basis D K E) (y : J → E) (j : J × D) : K :=
  b.repr (y j.1) j.2

@[simp] theorem unpack_pack (b : Module.Basis D K E) (x : I × D → K) :
    unpackOutputs b (packInputs b x) = x := by
  classical
  ext ⟨i, d⟩
  simp [unpackOutputs, packInputs, Finsupp.single_apply]

@[simp] theorem pack_unpack (b : Module.Basis D K E) (y : I → E) :
    packInputs b (unpackOutputs b y) = y := by
  ext i
  exact b.sum_repr (y i)

/-- Matrix of an extension-field operator in the array of ground-field
coordinates. Each block is multiplication by the corresponding extension scalar. -/
def restrictMatrix (b : Module.Basis D K E) (M : Matrix J I E) : Matrix (J × D) (I × D) K :=
  fun j i ↦ b.repr (M j.1 i.1 * b i.2) j.2

/-- Applying a word over the extension and unpacking the result computes the
base matrix obtained by replacing each entry with its scalar multiplication block. -/
theorem restrictMatrix_mulVec [Fintype I] (b : Module.Basis D K E) (M : Matrix J I E)
    (x : I × D → K) :
    (restrictMatrix b M).mulVec x = unpackOutputs b (M.mulVec (packInputs b x)) := by
  classical
  ext ⟨j, d⟩
  simp only [restrictMatrix, unpackOutputs, packInputs, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- Scalar restriction respects composition, so a product of layers may be
expanded one layer at a time. -/
theorem restrictMatrix_mul [Fintype J] (b : Module.Basis D K E)
    (A : Matrix H J E) (B : Matrix J I E) :
    restrictMatrix b (A * B) = restrictMatrix b A * restrictMatrix b B := by
  classical
  ext ⟨h, t⟩ ⟨i, s⟩
  simp only [restrictMatrix, Matrix.mul_apply, Finset.sum_mul, map_sum,
    Finsupp.finsetSum_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc]
  calc
    _ = (b.repr (A h j * ∑ d, b.repr (B j i * b s) d • b d)) t := by rw [b.sum_repr]
    _ = _ := by
      simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.finsetSum_apply,
        Finsupp.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro d _
      ring

omit [Fintype D] in
/-- A base-field matrix acts independently on each of the packed inputs, as in
the descent identity of the grid theorem. -/
theorem restrictMatrix_algebraMap [DecidableEq D] (b : Module.Basis D K E) (M : Matrix J I K) :
    restrictMatrix b (M.map (algebraMap K E)) =
      fun j i ↦ if j.2 = i.2 then M j.1 i.1 else 0 := by
  ext ⟨j, d⟩ ⟨i, u⟩
  simp [restrictMatrix, ← Algebra.smul_def, Finsupp.single_apply, eq_comm]

/-- The formula using the power basis `1,ζ,…,ζ^(e-1)` of a simple extension. -/
theorem mulVec_packed_powers [Fintype I] (b : PowerBasis K E) (M : Matrix J I K)
    (x : Fin b.dim → I → K) (j : J) :
    (M.map (algebraMap K E)).mulVec
        (fun i ↦ ∑ d : Fin b.dim, b.gen ^ (d : ℕ) * algebraMap K E (x d i)) j =
      ∑ d : Fin b.dim, b.gen ^ (d : ℕ) * algebraMap K E (M.mulVec (x d) j) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro i _
  ring

end

end FiniteFourier
end LinearAlgebra
end OAI
