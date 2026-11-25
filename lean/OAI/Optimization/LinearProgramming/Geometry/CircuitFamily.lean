import OAI.Optimization.LinearProgramming.Geometry.Basic
import OAI.Optimization.LinearProgramming.Geometry.Circuits
import OAI.Optimization.LinearProgramming.Geometry.Clipping

/-! The finite compressed circuit family and its active set in Section 2. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Submodule
open scoped Matrix BigOperators

variable {ι : Type*} [Fintype ι] {k : ℕ}

/-- A code specifies the fixed columns of the minor and the overall orientation. -/
noncomputable def signedCircuit (D : Matrix (Fin (k + 1)) ι ℝ)
    (code : (Fin k → ι) × Bool) : ι → ℝ :=
  if code.2 then -(circuitMinor D code.1) else circuitMinor D code.1

/-- The finite family includes only nonzero, nonnegative, full-height representatives. -/
noncomputable def circuitCodes (D : Matrix (Fin (k + 1)) ι ℝ) : Finset ((Fin k → ι) × Bool) := by
  classical
  exact Finset.univ.filter fun code => Function.Injective code.1 ∧
    0 ≤ signedCircuit D code ∧ signedCircuit D code ≠ 0

@[simp] theorem mem_circuitCodes {D : Matrix (Fin (k + 1)) ι ℝ}
    {code : (Fin k → ι) × Bool} : code ∈ circuitCodes D ↔ Function.Injective code.1 ∧
      0 ≤ signedCircuit D code ∧ signedCircuit D code ≠ 0 := by
  classical
  simp [circuitCodes]

/-- At zero prices this is the compression followed by sup-norm normalization in the definition of `rᵢ`. -/
noncomputable def compressedCircuitFamily (D : Matrix (Fin (k + 1)) ι ℝ)
    (f : (Fin k → ι) → ι → ℝ) : Finset (ι → ℝ) := by
  classical
  exact (circuitCodes D).image fun code => normalizedMinorRow (signedCircuit D code) (f code.1) 0

@[simp] theorem mem_compressedCircuitFamily {D : Matrix (Fin (k + 1)) ι ℝ}
    {f : (Fin k → ι) → ι → ℝ} {x : ι → ℝ} : x ∈ compressedCircuitFamily D f ↔
    ∃ code ∈ circuitCodes D, normalizedMinorRow (signedCircuit D code) (f code.1) 0 = x := by
  classical
  simp [compressedCircuitFamily]

omit [Fintype ι] in
private lemma pricedMinorRow_nonnegative {x : ι → ℝ} (h : 0 ≤ x) (f t : ι → ℝ) :
    0 ≤ pricedMinorRow x f t := by
  intro i
  rcases (h i).eq_or_lt with hi | hi
  · simp [pricedMinorRow, ← hi]
  · simp [pricedMinorRow, sign_pos hi, Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

private lemma normalizedMinorRow_pos_iff {x : ι → ℝ} (h : 0 ≤ x) (f t : ι → ℝ) (i : ι) :
    0 < normalizedMinorRow x f t i ↔ 0 < x i := by
  rcases (h i).eq_or_lt with hi | hi
  · simp [normalizedMinorRow, pricedMinorRow, ← hi]
  · have hp : 0 < pricedMinorRow x f t i := by
      simp [pricedMinorRow, sign_pos hi, Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hn : 0 < ‖pricedMinorRow x f t‖ := norm_pos_iff.mpr (fun hz => hp.ne' (congrFun hz i))
    exact iff_of_true (mul_pos (inv_pos.mpr hn) hp) hi

/-- Every member of the finite family lies in the unit cube. -/
theorem compressedCircuitFamily_unitCube {D : Matrix (Fin (k + 1)) ι ℝ}
    {f : (Fin k → ι) → ι → ℝ} {x : ι → ℝ} (hx : x ∈ compressedCircuitFamily D f) (i : ι) :
    0 ≤ x i ∧ x i ≤ 1 := by
  obtain ⟨code, hc, rfl⟩ := mem_compressedCircuitFamily.mp hx
  exact ⟨mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    (pricedMinorRow_nonnegative (mem_circuitCodes.mp hc).2.1 _ _ i),
    (le_abs_self _).trans (abs_normalizedMinorRow_le_one _ _ _ _)⟩

/-- The coordinates with finite hidden cost are exactly those having a nonnegative row-space
witness positive there. The assignment to minor logarithms does not change this active set. -/
theorem circuitEnvelope_pos_iff_rowSpan_witness (D : Matrix (Fin (k + 1)) ι ℝ)
    (hD : LinearIndependent ℝ D.row) (f : (Fin k → ι) → ι → ℝ) (i : ι) :
    0 < circuitEnvelope (compressedCircuitFamily D f) i ↔
      ∃ x ∈ span ℝ (Set.range D.row), 0 ≤ x ∧ 0 < x i := by
  constructor
  · intro h
    obtain ⟨x, hx, hxi⟩ := circuitEnvelope_attained h
    obtain ⟨code, hc, rfl⟩ := mem_compressedCircuitFamily.mp hx
    have hc0 := (mem_circuitCodes.mp hc).2.1
    refine ⟨signedCircuit D code, ?_, hc0, (normalizedMinorRow_pos_iff hc0 _ _ i).mp (hxi.symm ▸ h)⟩
    unfold signedCircuit
    split
    · exact Submodule.neg_mem _ (circuitMinor_mem_rowSpan _ _)
    · exact circuitMinor_mem_rowSpan _ _
  · rintro ⟨x, hxW, hx0, hxi⟩
    obtain ⟨J, hJ, _, hor⟩ := exists_nonnegative_circuitMinor D hD i hxW hx0 hxi
    have lift (code : (Fin k → ι) × Bool) (hJ : Function.Injective code.1)
        (hc0 : 0 ≤ signedCircuit D code) (hp : 0 < signedCircuit D code i) :
        0 < circuitEnvelope (compressedCircuitFamily D f) i := by
      have hc : code ∈ circuitCodes D := mem_circuitCodes.mpr ⟨hJ, hc0, fun hz => hp.ne' (congrFun hz i)⟩
      exact ((normalizedMinorRow_pos_iff hc0 _ _ i).mpr hp).trans_le
        (le_circuitEnvelope (mem_compressedCircuitFamily.mpr ⟨code, hc, rfl⟩) i)
    rcases hor with ⟨hc, hp⟩ | ⟨hc, hp⟩
    · exact lift (J, false) hJ hc hp
    · exact lift (J, true) hJ hc hp

/-- Bounded minor logarithms put each active coordinate of a normalized nonnegative
circuit between `2^(-2F)` and one, even when other coordinates vanish. -/
private theorem normalizedMinorRow_lower {x f : ι → ℝ} {F : ℝ} (hx : 0 ≤ x)
    (hb : ∀ j, x j ≠ 0 → |f j| ≤ F) (i : ι) (hi : 0 < x i) :
    (2 : ℝ) ^ (-(2 * F)) ≤ normalizedMinorRow x f 0 i := by
  let a := pricedMinorRow x f (0 : ι → ℝ)
  have ai (j : ι) (hj : 0 < x j) : a j = (2 : ℝ) ^ (f j) := by
    simp [a, pricedMinorRow, sign_pos hj]
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr fun hzero => by
    have heq : (2 : ℝ) ^ (f i) = 0 := (ai i hi).symm.trans (congrFun hzero i)
    exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne' heq
  have hmax : ‖a‖ ≤ (2 : ℝ)^F := by
    apply (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg (by norm_num) _)).mpr
    intro j
    rcases (hx j).eq_or_lt with hj | hj
    · simp [a, pricedMinorRow, ← hj, Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    · rw [ai j hj, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (abs_le.mp (hb j hj.ne')).2
  have hmin := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (abs_le.mp (hb i hi.ne')).1
  change (2 : ℝ) ^ (-(2 * F)) ≤ ‖a‖⁻¹ * a i
  rw [mul_comm (‖a‖⁻¹) (a i), ← div_eq_mul_inv, le_div_iff₀ hn, ai i hi]
  calc
    (2 : ℝ)^(-(2 * F)) * ‖a‖ ≤ 2^(-(2 * F)) * 2^F := by gcongr
    _ = (2 : ℝ)^(-F) := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
    _ ≤ (2 : ℝ)^(f i) := hmin

/-- The full-assignment bound on minor logs gives `0 ≤ rᵢ ≤ 2F` at every active coordinate. -/
theorem circuitCost_mem_Icc (D : Matrix (Fin (k + 1)) ι ℝ) (f : (Fin k → ι) → ι → ℝ)
    {F : ℝ} (hb : ∀ J j, circuitMinor D J j ≠ 0 → |f J j| ≤ F) (i : ι)
    (hpos : 0 < circuitEnvelope (compressedCircuitFamily D f) i) :
    circuitCost (compressedCircuitFamily D f) i ∈ Set.Icc 0 (2 * F) := by
  obtain ⟨x, hx, hxi⟩ := circuitEnvelope_attained hpos
  have hupper := (compressedCircuitFamily_unitCube hx i).2
  obtain ⟨c, hc, rfl⟩ := mem_compressedCircuitFamily.mp hx
  have hc0 := (mem_circuitCodes.mp hc).2.1
  have hci := (normalizedMinorRow_pos_iff hc0 _ _ i).mp (hxi.symm ▸ hpos)
  have hbf (j : ι) (hj : signedCircuit D c j ≠ 0) : |f c.1 j| ≤ F := by
    apply hb
    intro heq
    apply hj
    unfold signedCircuit
    split <;> simp [heq]
  have hlower := normalizedMinorRow_lower hc0 hbf i hci
  rw [hxi] at hupper hlower
  constructor
  · exact neg_nonneg.mpr (Real.logb_nonpos (by norm_num) hpos.le hupper)
  · exact neg_le.mp ((Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hpos).2 hlower)

/-- A zero-rank basis contributes no circuit representatives. -/
noncomputable def fullCircuitFamily (r : ℕ) :
    Matrix (Fin r) ι ℝ → ((Fin (r - 1) → ι) → ι → ℝ) → Finset (ι → ℝ) :=
  match r with
  | 0 => fun _ _ => ∅
  | _ + 1 => compressedCircuitFamily

/-- The active-set characterization includes the possibility of an empty primal or dual basis. -/
theorem fullCircuitEnvelope_pos_iff {r : ℕ} (D : Matrix (Fin r) ι ℝ)
    (hD : LinearIndependent ℝ D.row) (f : (Fin (r - 1) → ι) → ι → ℝ) (i : ι) :
    0 < circuitEnvelope (fullCircuitFamily r D f) i ↔
      ∃ x ∈ span ℝ (Set.range D.row), 0 ≤ x ∧ 0 < x i := by
  cases r with
  | zero => simp [fullCircuitFamily, circuitEnvelope]
  | succ k => exact circuitEnvelope_pos_iff_rowSpan_witness D hD f i

end Geometry
end LinearProgramming
end Optimization
end OAI
