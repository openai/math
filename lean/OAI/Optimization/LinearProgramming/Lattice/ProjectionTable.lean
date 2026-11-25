import OAI.Optimization.LinearProgramming.Lattice.ProjectionMatrix

/-! Eager evaluation of rational residual matrices on dense vectors. -/

open scoped BigOperators
open Matrix

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

variable {p : ℕ}

private theorem foldl_add_sum {R : Type*} [AddCommMonoid R] {n : ℕ}
    (f : Fin n → R) (a : R) : Fin.foldl n (fun s i => s + f i) a = a + ∑ i, f i := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Fin.foldl_succ, ih, Fin.sum_univ_succ, add_assoc]

/-- A flat finite loop reads and multiplies each coordinate exactly once. -/
def tableDot (a b : Fin p → ℚ) : ℚ := Fin.foldl p (fun s i => s + a i * b i) 0

private theorem tableDot_eq (a b : Fin p → ℚ) : tableDot a b = a ⬝ᵥ b := by
  simp [tableDot, foldl_add_sum, dotProduct]

/-- A strict array of rows, each a strict array of entries. -/
abbrev ProjectionTable (p : ℕ) := Vector (Vector ℚ p) p

def readProjectionTable (t : ProjectionTable p) : Matrix (Fin p) (Fin p) ℚ :=
  fun i j => t[i][j]

private def writeProjectionTable (a : Matrix (Fin p) (Fin p) ℚ) : ProjectionTable p :=
  Vector.ofFn fun i => Vector.ofFn fun j => a i j

private theorem read_write_table (a : Matrix (Fin p) (Fin p) ℚ) :
    readProjectionTable (writeProjectionTable a) = a := by
  ext i j
  simp [readProjectionTable, writeProjectionTable]

/-- Update the old matrix in quadratic scalar work. The vectors `u = Pz` and
`r = uᵀP` are materialized once before writing the new entries. -/
def stepProjectionTable (t : ProjectionTable p) (z : Fin p → ℤ) : ProjectionTable p :=
  let qz : Vector ℚ p := Vector.ofFn fun j => (z j : ℚ)
  let u : Vector ℚ p := Vector.ofFn fun i => tableDot (fun j => t[i][j]) (fun j => qz[j])
  let d := tableDot (fun i => u[i]) (fun i => u[i])
  if d = 0 then t else
    let r : Vector ℚ p := Vector.ofFn fun j => tableDot (fun i => u[i]) (fun i => t[i][j])
    let s : Vector ℚ p := Vector.ofFn fun i => u[i] / d
    writeProjectionTable (fun i j => t[i][j] - s[i] * r[j])

private theorem product_lineComplement_apply (P : Matrix (Fin p) (Fin p) ℚ) (u : Fin p → ℚ)
    (i j : Fin p) :
    (rationalLineComplement u * P) i j = P i j - u i / (u ⬝ᵥ u) * (u ᵥ* P) j := by
  have hentry (k : Fin p) : rationalLineComplement u i k =
      (1 : Matrix (Fin p) (Fin p) ℚ) i k - u i * u k / (u ⬝ᵥ u) := by
    by_cases h : u ⬝ᵥ u = 0 <;> simp [rationalLineComplement, h]
  rw [Matrix.mul_apply]
  simp_rw [hentry, sub_mul]
  rw [Finset.sum_sub_distrib]
  have hone : (∑ k, (1 : Matrix (Fin p) (Fin p) ℚ) i k * P k j) = P i j :=
    congrFun (congrFun (Matrix.one_mul P) i) j
  rw [hone]
  congr 1
  change _ = (u i / (u ⬝ᵥ u)) * ∑ k, u k * P k j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem read_step_table (t : ProjectionTable p) (z : Fin p → ℤ) :
    readProjectionTable (stepProjectionTable t z) =
      rationalLineComplement (readProjectionTable t *ᵥ fun i => (z i : ℚ)) * readProjectionTable t := by
  let P := readProjectionTable t
  let u := P *ᵥ fun i => (z i : ℚ)
  let update : Matrix (Fin p) (Fin p) ℚ :=
    fun i j => P i j - u i / (u ⬝ᵥ u) * (u ᵥ* P) j
  have hstep : stepProjectionTable t z =
      (if u ⬝ᵥ u = 0 then t else writeProjectionTable update) := by
    simp only [stepProjectionTable, tableDot_eq, Fin.getElem_fin, Vector.getElem_ofFn]
    rfl
  rw [hstep]
  ext i j
  rw [product_lineComplement_apply]
  change readProjectionTable (if u ⬝ᵥ u = 0 then t else writeProjectionTable update) i j =
    P i j - u i / (u ⬝ᵥ u) * (u ᵥ* P) j
  by_cases h : u ⬝ᵥ u = 0
  · simp [h, P]
  · simpa only [h, ↓reduceIte] using congrFun (congrFun (read_write_table update) i) j

/-- Form every intermediate matrix once, starting with the materialized identity matrix. -/
def materializedProjection : List (Fin p → ℤ) → ProjectionTable p
  | [] => writeProjectionTable 1
  | z :: zs => stepProjectionTable (materializedProjection zs) z

/-- Coordinate formula used by the packed rational implementation. -/
theorem rationalLineComplement_mul_entry (P : Matrix (Fin p) (Fin p) ℚ) (u : Fin p → ℚ)
    (i j : Fin p) : (rationalLineComplement u * P) i j =
    P i j - u i / (u ⬝ᵥ u) * (u ᵥ* P) j := product_lineComplement_apply P u i j

/-- Matrix view with constant-index reads of the fully materialized rational projector. -/
def residualTableMatrix (zs : List (Fin p → ℤ)) : Matrix (Fin p) (Fin p) ℚ :=
  readProjectionTable (materializedProjection zs)

theorem residualTableMatrix_eq (zs : List (Fin p → ℤ)) :
    residualTableMatrix zs = rationalResidualMatrix zs := by
  induction zs with
  | nil => exact read_write_table _
  | cons z zs ih =>
    change readProjectionTable (stepProjectionTable (materializedProjection zs) z) = _
    rw [read_step_table, show readProjectionTable (materializedProjection zs) = _ from ih]
    rfl

end Lattice
end LinearProgramming
end Optimization
end OAI
