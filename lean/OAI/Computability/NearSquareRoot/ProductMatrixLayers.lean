import OAI.Computability.NearSquareRoot.SynchronizedNorm
import OAI.Computability.NearSquareRoot.PrecisionLayers
import OAI.Computability.NearSquareRoot.PrecisionMixed

/-!
# Chronological execution of a fixed-point transform

A factorization lists its leftmost factor first. Matrix-vector execution applies
its factors from right to left. For the adjoint transform the order reverses and
each individual matrix is replaced by its conjugate transpose.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductMatrixLayers

open Matrix WithLp SynchronizedPadding
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Square (ι : Type*) := Matrix ι ι ℂ

/-- The instruction at tick `j` of a right-to-left matrix product. -/
def atTick (ms : List (Square ι)) (j : ℕ) : Square ι := ms.reverse[j]?.getD 1

def UnitaryFactors (ms : List (Square ι)) : Prop := ∀ M ∈ ms, Mᴴ * M = 1

theorem unitary_atTick {ms : List (Square ι)} (h : UnitaryFactors ms) (j : ℕ) :
    (atTick ms j)ᴴ * atTick ms j = 1 := by
  unfold atTick
  cases e : ms.reverse[j]? with
  | none => simp
  | some m =>
    exact h m (List.mem_reverse.mp (List.mem_of_getElem? e))

/-- Execute the exact local isometry of the current factor. -/
def ideal (ms : List (Square ι)) (h : UnitaryFactors ms) (j : ℕ) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  (matrixIsometry _ (unitary_atTick h j)).toLinearIsometry

theorem execute_prefix (ms : List (Square ι)) (h : UnitaryFactors ms) (x : ι → ℂ)
    {j : ℕ} (hj : j ≤ ms.length) :
    exactLayerPrefix (ideal ms h) (toLp 2 x) j =
      toLp 2 ((ms.reverse.take j).reverse.prod *ᵥ x) := by
  induction j with
  | zero => simp [exactLayerPrefix]
  | succ j ih =>
    have hj' : j < ms.reverse.length := by simpa using hj
    rw [exactLayerPrefix, ih (by omega), List.take_succ_eq_append_getElem hj']
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.prod_cons, ideal, LinearIsometryEquiv.coe_toLinearIsometry, matrixIsometry_apply]
    simp [atTick, List.getElem?_eq_getElem hj', Matrix.mulVec_mulVec]

theorem execute (ms : List (Square ι)) (h : UnitaryFactors ms) (x : EuclideanSpace ℂ ι) :
    exactLayerPrefix (ideal ms h) x ms.length = toLp 2 (ms.prod *ᵥ ofLp x) := by
  simpa [List.take_of_length_le (show ms.reverse.length ≤ ms.length by simp)] using
    execute_prefix ms h (ofLp x) (le_refl ms.length)

/-- Factorization whose matrix product is the adjoint of the original product. -/
def adjointFactors (ms : List (Square ι)) := ms.reverse.map Matrix.conjTranspose

theorem prod_adjointFactors (ms : List (Square ι)) :
    (adjointFactors ms).prod = ms.prodᴴ := by
  induction ms with
  | nil => simp [adjointFactors]
  | cons m ms ih =>
    simp only [adjointFactors, List.reverse_cons, List.map_append, List.map_singleton,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one, conjTranspose_mul] at *
    rw [ih]

theorem unitary_adjointFactors {ms : List (Square ι)} (h : UnitaryFactors ms) :
    UnitaryFactors (adjointFactors ms) := by
  intro M hM
  obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hM
  rw [conjTranspose_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_unitaryGroup_iff'.mpr (h N (List.mem_reverse.mp hN)))

theorem execute_adjoint (ms : List (Square ι)) (h : UnitaryFactors ms)
    (x : EuclideanSpace ℂ ι) :
    exactLayerPrefix (ideal _ (unitary_adjointFactors h)) x (adjointFactors ms).length =
      toLp 2 (ms.prodᴴ *ᵥ ofLp x) := by
  rw [execute, prod_adjointFactors]

end
end ProductMatrixLayers

namespace ProductRecovery

open IntegerMultiplication FixedPoint
noncomputable section
variable {ι : Type} [Fintype ι]

/-- Exact and fixed-point actions of the layers in one direction of the transform. -/
structure Layers (ι : Type) [Fintype ι] (k : ℕ) where
  count : ℕ
  ideal : ℕ → EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι
  apply : ℕ → (ι → Record k) → (ι → Record k)

namespace Layers

variable {k : ℕ}
abbrev Space (ι : Type) [Fintype ι] := EuclideanSpace ℂ ι

/-- Execute a prefix of the rounded program on its actual input records. -/
def run (p : Layers ι k) (r : ι → Record k) : ℕ → (ι → Record k)
  | 0 => r
  | j+1 => p.apply j (p.run r j)

/-- Local error is required only on represented streams in the working range. -/
structure Approximates (p : Layers ι k) (U : Space ι →ₗᵢ[ℂ] Space ι) : Prop where
  depth : p.count ≤ 2 ^ (10*k)
  factorization : ∀ x, exactLayerPrefix p.ideal x p.count = U x
  localError : ∀ j < p.count, ∀ r : ι → Record k, ‖recordArray r‖ ≤ (2 : ℝ) ^ (13*k) →
    ‖recordArray (p.apply j r) - p.ideal j (recordArray r)‖ ≤ 1 / (2 : ℝ) ^ (50*k)

/-- The accumulated error of all completed layers. -/
theorem Approximates.error {p : Layers ι k} {U : Space ι →ₗᵢ[ℂ] Space ι}
    (h : p.Approximates U) (hk : 1 ≤ k) (r : ι → Record k)
    (hr : ‖recordArray r‖ ≤ (2 : ℝ)^(12*k)) :
    ‖recordArray (p.run r p.count) - U (recordArray r)‖ ≤ 1 / (2 : ℝ)^(40*k) := by
  let v j := recordArray (p.run r j)
  have he := (transformLayerPrecision p.ideal v hk h.depth hr
    (fun j hj => h.localError j hj _) (le_refl p.count)).1
  simpa only [v, run, h.factorization] using he

end Layers

namespace Layers

open ProductMatrixLayers SynchronizedPadding Matrix WithLp

variable {k : ℕ} [DecidableEq ι]

/-- The fixed-point instruction at each tick implements the corresponding matrix in
the factorization, in the physical application order (rightmost first). -/
def fromMatrices (ms : List (Square ι)) (h : UnitaryFactors ms)
    (apply : ℕ → (ι → Record k) → (ι → Record k)) : Layers ι k :=
  ⟨ms.length, ProductMatrixLayers.ideal ms h, apply⟩

/-- Supply only the verified local rounding error and the exact matrix factorization;
the action of the whole stream of rounded instructions follows. -/
theorem fromMatrices_approximates (ms : List (Square ι)) (h : UnitaryFactors ms)
    (apply : ℕ → (ι → Record k) → (ι → Record k))
    (depth : ms.length ≤ 2^(10*k))
    (err : ∀ j < ms.length, ∀ r : ι → Record k, ‖recordArray r‖ ≤ (2 : ℝ)^(13*k) →
      ‖recordArray (apply j r) - ProductMatrixLayers.ideal ms h j (recordArray r)‖ ≤ 1 / (2 : ℝ)^(50*k))
    (M : Square ι) (hM : Mᴴ * M = 1) (factor : ms.prod = M) :
    (fromMatrices ms h apply).Approximates (matrixIsometry M hM).toLinearIsometry := by
  refine ⟨depth, ?_, err⟩
  intro x
  change exactLayerPrefix (ProductMatrixLayers.ideal ms h) x ms.length = matrixIsometry M hM x
  rw [execute, factor]
  exact (matrixIsometry_apply M hM (ofLp x)).symm

/-- Execute the adjoints in reverse order using the same depth. -/
theorem fromAdjoints_approximates (ms : List (Square ι)) (h : UnitaryFactors ms)
    (apply : ℕ → (ι → Record k) → (ι → Record k))
    (depth : ms.length ≤ 2^(10*k))
    (err : ∀ j < ms.length, ∀ r : ι → Record k, ‖recordArray r‖ ≤ (2 : ℝ)^(13*k) →
      ‖recordArray (apply j r) - ProductMatrixLayers.ideal (adjointFactors ms) (unitary_adjointFactors h) j
        (recordArray r)‖ ≤ 1 / (2 : ℝ)^(50*k))
    (M : Square ι) (hM : Mᴴ * M = 1) (factor : ms.prod = M) :
    (fromMatrices (adjointFactors ms) (unitary_adjointFactors h) apply).Approximates
      (matrixIsometry M hM).symm.toLinearIsometry := by
  refine ⟨by simpa [fromMatrices, adjointFactors] using depth, ?_, by simpa only [fromMatrices, adjointFactors, List.length_map, List.length_reverse] using err⟩
  intro x
  change exactLayerPrefix (ProductMatrixLayers.ideal _ (unitary_adjointFactors h)) x
    (adjointFactors ms).length = (matrixIsometry M hM).symm x
  rw [execute_adjoint ms h x, factor]
  exact (matrixIsometry_symm_apply M hM (ofLp x)).symm

/-- A permutation of the actual record slots is exact, including all entries of
the padding. Matrix row `i` reads the input at position `e i`. -/
theorem record_permutation (e : Equiv.Perm ι) (r : ι → Record k)
    (h : (e.toPEquiv.toMatrix : Square ι)ᴴ * e.toPEquiv.toMatrix = 1) :
    recordArray (r ∘ e) = matrixIsometry _ h (recordArray r) := by
  apply WithLp.ofLp_injective
  funext i
  change value k (r (e i)) = (e.toPEquiv.toMatrix *ᵥ (fun j => value k (r j))) i
  simp [mulVec, dotProduct, PEquiv.toMatrix_apply]

/-- A diagonal changes each record by an actual fixed-width complex multiplication.
The streamed coefficient error and the final arithmetic truncation are both charged
in the local layer budget. -/
theorem record_diagonal_error {pc wc : ℕ} (hk : 1 ≤ k) (hcard : Fintype.card ι = 2^k)
    (c : ι → ℂ) (hc : ∀ i, ‖c i‖ = 1) (cs : ι → Dusk.Grain wc) (r : ι → Record k)
    (hcs : ∀ i, ‖Grid.meaning pc wc (cs i) - c i‖ ≤ 1 / (2 : ℝ)^(70*k))
    (hr : ‖recordArray r‖ ≤ (2 : ℝ)^(13*k))
    (h : (diagonal c)ᴴ * diagonal c = 1) :
    ‖recordArray (fun i => multiplyCoefficient pc (r i) (cs i)) -
      matrixIsometry (diagonal c) h (recordArray r)‖ ≤ 1 / (2 : ℝ)^(50*k) := by
  have hv : matrixIsometry (diagonal c) h (recordArray r) =
      phaseLayerIsometry c hc (recordArray r) := by
    apply WithLp.ofLp_injective
    funext i
    exact Matrix.mulVec_diagonal c _ i
  rw [hv]
  exact applyPhase_error hk hcard r cs c hc hr hcs

end Layers
end
end ProductRecovery

end NearSquareRoot
end Computability
end OAI
