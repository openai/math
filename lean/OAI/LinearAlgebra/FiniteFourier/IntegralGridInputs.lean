import OAI.LinearAlgebra.FiniteFourier.GridInputs
import OAI.LinearAlgebra.FiniteFourier.FixedConvolution

/-! # Specializing the two integral companion constructions

The fixed-convolution hypothesis comes from the formal integer polynomial
multiplication circuit. The tensor-power shear hypothesis comes from integer
binary linear gates. In both cases exactly the same cost bound works in every
characteristic.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

section MapCoefficients

variable {R K I O W : Type*} [Semiring R] [Semiring K]

private def BinaryGate.mapCoeff (g : BinaryGate R W) (φ : R →+* K) : BinaryGate K W :=
  ⟨g.left, g.right, φ g.leftCoeff, φ g.rightCoeff⟩

private def Readout.mapCoeff (z : Readout R W) (φ : R →+* K) : Readout K W :=
  match z with
  | .zero => .zero
  | .scaled c w => .scaled (φ c) w

/-- Change the coefficient semiring of a straight-line program. -/
def Program.mapCoeff (φ : R →+* K) : {s : ℕ} → Program R I s → Program K I s
  | _, .nil => .nil
  | _, .step p g => .step (p.mapCoeff φ) (g.mapCoeff φ)

private theorem Program.value_mapCoeff (φ : R →+* K) {s : ℕ} (p : Program R I s) (x : I → R) :
    (p.mapCoeff φ).value (fun i => φ (x i)) = fun j => φ (p.value x j) := by
  induction p with
  | nil => funext j; exact j.elim0
  | step p g ih =>
    have hw (w : I ⊕ _) : Sum.elim (fun i => φ (x i)) ((p.mapCoeff φ).value (fun i => φ (x i))) w =
        φ (Sum.elim x (p.value x) w) := by cases w <;> simp [ih]
    funext j
    refine Fin.cases ?_ (fun k => congrFun ih k) j
    change (g.mapCoeff φ).eval _ = φ (g.eval _)
    simp only [BinaryGate.mapCoeff, BinaryGate.eval, map_add, map_mul, hw]

/-- Specialization preserves the exact number of gates and maps all readout weights. -/
def Circuit.mapCoeff {s : ℕ} (p : Circuit R I O s) (φ : R →+* K) : Circuit K I O s :=
  ⟨p.program.mapCoeff φ, fun o => (p.output o).mapCoeff φ⟩

theorem Circuit.eval_mapCoeff {s : ℕ} (p : Circuit R I O s) (φ : R →+* K)
    (x : I → R) (o : O) :
    (p.mapCoeff φ).eval (fun i => φ (x i)) o = φ (p.eval x o) := by
  simp only [eval, mapCoeff, Program.value_mapCoeff]
  cases p.output o with
  | zero => simp [Readout.mapCoeff, Readout.eval]
  | scaled c w => cases w <;> simp [Readout.mapCoeff, Readout.eval]

theorem Circuit.matrix_mapCoeff {s : ℕ} (p : Circuit R I O s) (φ : R →+* K) :
    (p.mapCoeff φ).matrix = p.matrix.map φ := by
  classical
  ext o i
  have he : (Pi.single i (1 : K) : I → K) = fun j => φ ((Pi.single i (1 : R) : I → R) j) := by
    funext j
    by_cases h : j = i <;> simp [h]
  change (p.mapCoeff φ).eval (Pi.single i 1) o = φ (p.eval (Pi.single i 1) o)
  rw [he, eval_mapCoeff]

end MapCoefficients

/-- Integral operation-count statement needed of the length-`n` formal convolution circuits. -/
def IntegralConvolutionBound (β C : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n →
    ∃ (r : ℕ) (p : MatrixMultiplication.Arithmetic.Program ℤ (Fin n ⊕ Fin n) r)
      (out : Fin (2*n-1) → Fin r), ComputesConvolution p out ∧
      (p.cost : ℝ) ≤ C * n * (1 + Real.logb 2 n) ^ β

/-- Integral linear gate count for the simultaneous tensor-power shear. -/
def IntegralShearBound (β C : ℝ) : Prop :=
  ∀ j : ℕ, ∃ (s : ℕ) (p : Circuit ℤ (Fin j → Fin 2) (Fin j → Fin 2) s),
    p.matrix = gridTensor (fun _ : Fin j => (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ)) ∧
    (s : ℝ) ≤ C * (2 : ℝ)^j * (1 + (j : ℝ))^β

/-- The two characteristic-independent integral circuit estimates in the
companion's Theorems 9.3 and 11.1, specialized to the operations used here. -/
def IntegralCircuitInputs : Prop :=
  ∀ β : ℝ, 1 / 2 < β → β < 1 → ∃ C > (0 : ℝ),
    IntegralConvolutionBound β C ∧ IntegralShearBound β C

/-- The convolution and shear constructions may choose their constants
independently. Their maximum works simultaneously in every characteristic. -/
theorem IntegralCircuitInputs.of_separate_bounds
    (conv : ∀ β : ℝ, 1 / 2 < β → β < 1 → ∃ C > (0 : ℝ), IntegralConvolutionBound β C)
    (shear : ∀ β : ℝ, 1 / 2 < β → β < 1 → ∃ D > (0 : ℝ), IntegralShearBound β D) :
    IntegralCircuitInputs := by
  intro β hβ hβ'
  obtain ⟨C, hC, hconv⟩ := conv β hβ hβ'
  obtain ⟨D, _, hshear⟩ := shear β hβ hβ'
  refine ⟨max C D, hC.trans_le (le_max_left ..), ?_, ?_⟩
  · intro n hn
    obtain ⟨r, p, o, hp, hs⟩ := hconv n hn
    refine ⟨r, p, o, hp, hs.trans ?_⟩
    have hlog := Real.logb_nonneg (by norm_num : 1 < (2:ℝ))
      (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left ..) (Nat.cast_nonneg _))
      (Real.rpow_nonneg (by linarith) _)
  · intro j
    obtain ⟨s, p, hp, hs⟩ := hshear j
    refine ⟨s, p, hp, hs.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))
      (Real.rpow_nonneg (by positivity) _)

theorem IntegralConvolutionBound.fixedConvolutionBound {β C : ℝ} (h : IntegralConvolutionBound β C)
    (K : Type*) [Field K] : FixedConvolutionBound K β C := by
  intro n hn f
  obtain ⟨r, p, out, hp, hs⟩ := h n hn
  exact (Nat.cast_le (α := ℝ) |>.mpr ((complexity_le_iff ..).2
    (hp.realizable_truncMatrix (Int.castRingHom K) f))).trans hs

theorem IntegralShearBound.shearTensorBound {β C : ℝ} (h : IntegralShearBound β C)
    (K : Type*) [CommRing K] : ShearTensorBound K β C := by
  intro j
  obtain ⟨s, p, hp, hs⟩ := h j
  apply le_trans _ hs
  apply Nat.cast_le (α := ℝ) |>.mpr
  apply (complexity_le_iff ..).2
  refine ⟨s, le_rfl, p.mapCoeff (Int.castRingHom K), ?_⟩
  rw [Circuit.matrix_mapCoeff, hp]
  ext x y
  simp only [gridTensor, Matrix.map_apply, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  generalize x i = x₀
  generalize y i = y₀
  fin_cases x₀ <;> fin_cases y₀ <;> simp [unitShear]

/-- Both estimates specialize together, with constants independent of the field. -/
theorem uniformGridInputs_of_integral_bounds
    (h : ∀ β : ℝ, 1 / 2 < β → β < 1 → ∃ C > (0 : ℝ),
      IntegralConvolutionBound β C ∧ IntegralShearBound β C) : UniformGridInputs := by
  intro β hβ hβ'
  obtain ⟨C, hC, hc, hs⟩ := h β hβ hβ'
  exact ⟨C, hC, fun K _ => ⟨hc.fixedConvolutionBound K, hs.shearTensorBound K⟩⟩

end FiniteFourier
end LinearAlgebra
end OAI
