import OAI.Optimization.LinearProgramming.Compression.Signed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The lattice test for a requested minor, Section 3.2. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- Integer linear form on the proxy logarithms for a single request. -/
def requestForm {d : ℕ} (x : Fin d → ℝ) (z : Fin d → ℤ) : ℝ := ∑ i, z i * x i

/-- Point in the real Euclidean realization of the rational graph lattice of `w`. -/
noncomputable def requestGraph {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  WithLp.toLp 2 (Fin.snoc (fun i => (z i : ℝ)) (requestForm (fun i => w i) z))

@[simp] theorem requestGraph_castSucc {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ) (i : Fin d) :
    requestGraph w z i.castSucc = z i := by simp [requestGraph]

@[simp] theorem requestGraph_last {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ) :
    requestGraph w z (Fin.last d) = requestForm (fun i => w i) z := by simp [requestGraph]

/-- A ternary relation of residual at most two is a short vector in the graph lattice. -/
theorem requestGraph_norm_sq_le {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ)
    (hcoeff : ∀ i, |(z i : ℝ)| ≤ 1) (hform : |requestForm (fun i => w i) z| ≤ 2) :
    ‖requestGraph w z‖ ^ 2 ≤ d + 4 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp only [requestGraph_castSucc, requestGraph_last]
  have hsum : ∑ i, (z i : ℝ) ^ 2 ≤ ∑ _ : Fin d, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hcoeff i) 2
  simp at hsum
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hform 2
  rw [sq_abs] at hsq
  linarith

/-- Every integer coordinate and the dot product of a short graph vector are bounded. -/
theorem requestGraph_coords_le {d : ℕ} {w : Fin d → ℚ} {z : Fin d → ℤ} {K : ℝ}
    (h : ‖requestGraph w z‖ ≤ K) :
    (∀ i, |(z i : ℝ)| ≤ K) ∧ |requestForm (fun i => w i) z| ≤ K := by
  constructor
  · intro i
    simpa only [Real.norm_eq_abs, requestGraph_castSucc] using
      (PiLp.norm_apply_le (requestGraph w z) i.castSucc).trans h
  · simpa only [Real.norm_eq_abs, requestGraph_last] using
      (PiLp.norm_apply_le (requestGraph w z) (Fin.last d)).trans h

/-- Norm cutoff used when inspecting the reduced graph basis. -/
def requestCutoff (d : ℕ) : ℕ := 2 ^ (d + 2) * (d + 3)

/-- The LLL norm bound on a ternary relation fits the request cutoff. -/
theorem requestGraph_reduction_bound {d : ℕ} {x : EuclideanSpace ℝ (Fin (d+1))}
    (hx : ‖x‖ ^ 2 ≤ d + 4) : (2 : ℝ) ^ d * ‖x‖ ≤ requestCutoff d := by
  have hn : ‖x‖ ≤ 4 * ((d : ℝ) + 3) := by
    nlinarith [norm_nonneg x, sq_nonneg ((d : ℝ) + 2), sq_nonneg (‖x‖ - 1)]
  have h := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (2 : ℝ)^d)
  push_cast [requestCutoff, pow_add]
  linarith only [h]

/-- If the LLL prefix spans a vector with nonzero designated coordinate, some inspected
basis vector is short and has nonzero designated coordinate. -/
theorem exists_short_request_basis_vector {d : ℕ} (w : Fin d → ℚ) (g : Fin d → Fin d → ℤ)
    (z : Fin d → ℤ) (last : Fin d) (hz : z last ≠ 0)
    (hshort : ‖requestGraph w z‖ ^ 2 ≤ d + 4)
    (hprefix : ∃ j : Fin d, requestGraph w z ∈
      Submodule.span ℝ ((fun i => requestGraph w (g i)) '' Set.Iic j) ∧
      ∀ i ≤ j, ‖requestGraph w (g i)‖ ≤ 2 ^ d * ‖requestGraph w z‖) :
    ∃ i, g i last ≠ 0 ∧ ‖requestGraph w (g i)‖ ≤ requestCutoff d := by
  obtain ⟨j, hspan, hsmall⟩ := hprefix
  have any : ∃ i ≤ j, g i last ≠ 0 := by
    by_contra! hall
    let ev : EuclideanSpace ℝ (Fin (d + 1)) →ₗ[ℝ] ℝ :=
      PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin (d+1) => ℝ) last.castSucc
    have hker : Submodule.span ℝ ((fun i => requestGraph w (g i)) '' Set.Iic j) ≤
        LinearMap.ker ev := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      change requestGraph w (g i) last.castSucc = 0
      simp [hall i hi]
    have hx := hker hspan
    change requestGraph w z last.castSucc = 0 at hx
    rw [requestGraph_castSucc, Int.cast_eq_zero] at hx
    exact hz hx
  obtain ⟨i, hi, hne⟩ := any
  exact ⟨i, hne, (hsmall i hi).trans (requestGraph_reduction_bound hshort)⟩

/-- What sign preservation on the augmented proxy vector gives after normalizing the
last coordinate to one. Bounds include the integer constant coefficient. -/
def RequestSigns {d : ℕ} (v w : Fin d → ℝ) (M : ℕ) : Prop :=
  ∀ (z : Fin d → ℤ) (c : ℤ), (∑ i, |(z i : ℝ)|) + |(c : ℝ)| ≤ M →
    (0 ≤ requestForm v z + c ↔ 0 ≤ requestForm w z + c)

@[simp] theorem requestForm_neg {d : ℕ} (v : Fin d → ℝ) (z : Fin d → ℤ) :
    requestForm v (-z) = -requestForm v z := by simp [requestForm, Finset.sum_neg_distrib]

theorem RequestSigns.abs_iff {d M : ℕ} {v w : Fin d → ℝ} (h : RequestSigns v w M)
    (z : Fin d → ℤ) (K : ℕ) (hbudget : (∑ i, |(z i : ℝ)|) + K ≤ M) :
    |requestForm v z| ≤ K ↔ |requestForm w z| ≤ K := by
  have hp := h z K (by simpa using hbudget)
  have hm := h (-z) K (by simpa using hbudget)
  simp only [requestForm_neg, Int.cast_natCast] at hp hm
  rw [abs_le, abs_le]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · linarith only [hp.mp (by linarith only [hlo])]
    · linarith only [hm.mp (by linarith only [hhi])]
  · rintro ⟨hlo, hhi⟩
    constructor
    · linarith only [hp.mpr (by linarith only [hlo])]
    · linarith only [hm.mpr (by linarith only [hhi])]

/-- Failure to find an inspectable basis element certifies dissociation of the enlarged
list. The two inputs are exactly the guarantees of the rounding and lattice lemmas. -/
theorem dissociated_of_request_search_empty {d : ℕ} (v : Fin d → ℝ) (w : Fin d → ℚ)
    (g : Fin d → Fin d → ℤ) (last : Fin d)
    (hprev : IsDissociated v (Finset.univ.erase last))
    (hsign : RequestSigns v (fun i => w i) ((d+2)*(requestCutoff d+3)))
    (hlll : ∀ z : Fin d → ℤ, z last ≠ 0 → ∃ j : Fin d, requestGraph w z ∈
      Submodule.span ℝ ((fun i => requestGraph w (g i)) '' Set.Iic j) ∧
      ∀ i ≤ j, ‖requestGraph w (g i)‖ ≤ 2 ^ d * ‖requestGraph w z‖)
    (hnone : ¬ ∃ i, g i last ≠ 0 ∧ ‖requestGraph w (g i)‖ ≤ requestCutoff d) :
    IsDissociated v Finset.univ := by
  by_contra hbad
  have hins : insert last (Finset.univ.erase last) = Finset.univ :=
    Finset.insert_erase (Finset.mem_univ _)
  obtain ⟨z, hz, hn, hr⟩ := exists_signed_of_not_isDissociated_insert v _ last
    (Finset.notMem_erase _ _) hprev (by rwa [hins])
  rw [hins] at hz hr
  have hone (i : Fin d) : |(z i : ℝ)| ≤ 1 := by
    rcases hz i (by simp) with hi | hi | hi <;> simp [hi]
  have hsum : ∑ i, |(z i : ℝ)| ≤ ∑ _ : Fin d, (1 : ℝ) :=
    Finset.sum_le_sum fun i _ => hone i
  simp at hsum
  change |requestForm v z| ≤ 2 at hr
  have hwr := (hsign.abs_iff z 2 (by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) (requestCutoff d)])).mp hr
  exact hnone (exists_short_request_basis_vector w g z last hn
    (requestGraph_norm_sq_le w z hone hwr) (hlll z hn))

/-- Dot product bound on the unrounded proxies for an accepted basis vector. -/
theorem abs_requestForm_le_of_basis {d : ℕ} (v : Fin d → ℝ) (w : Fin d → ℚ)
    (z : Fin d → ℤ) (hsign : RequestSigns v (fun i => w i) ((d+2)*(requestCutoff d+3)))
    (hshort : ‖requestGraph w z‖ ≤ requestCutoff d) :
    |requestForm v z| ≤ requestCutoff d := by
  obtain ⟨hc, hr⟩ := requestGraph_coords_le hshort
  have hsum : ∑ i, |(z i : ℝ)| ≤ ∑ _ : Fin d, (requestCutoff d : ℝ) :=
    Finset.sum_le_sum fun i _ => hc i
  simp [nsmul_eq_mul] at hsum
  exact (hsign.abs_iff z (requestCutoff d) (by
    push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) d, Nat.cast_nonneg (α := ℝ) (requestCutoff d)])).mpr hr

/-- The exact rational slope obtained by solving for the newly requested coordinate. -/
def requestSlope {n : ℕ} (z : Fin (n+1) → ℤ) (i : Fin n) : ℚ :=
  -(z i.castSucc : ℚ) / z (Fin.last n)

theorem request_affine_identity {n : ℕ} (v : Fin (n+1) → ℝ) (z : Fin (n+1) → ℤ)
    (hz : z (Fin.last n) ≠ 0) :
    v (Fin.last n) = ∑ i : Fin n, (requestSlope z i : ℝ) * v i.castSucc +
      requestForm v z / (z (Fin.last n) : ℝ) := by
  have hn : (z (Fin.last n) : ℝ) ≠ 0 := by exact_mod_cast hz
  rw [requestForm, Fin.sum_univ_castSucc]
  simp only [requestSlope, Rat.cast_div, Rat.cast_neg, Rat.cast_intCast, neg_div,
    div_mul_eq_mul_div, neg_mul, ← Finset.sum_div, Finset.sum_neg_distrib]
  field_simp
  ring

theorem request_residual_le {d : ℕ} (v : Fin d → ℝ) (z : Fin d → ℤ) (last : Fin d)
    {K : ℝ} (hz : z last ≠ 0) (hform : |requestForm v z| ≤ K) :
    |requestForm v z / (z last : ℝ)| ≤ K := by
  have hden : (1 : ℝ) ≤ |(z last : ℝ)| := by
    exact_mod_cast Int.one_le_abs hz
  rw [abs_div, div_le_iff₀ (by linarith only [hden])]
  have hK := (abs_nonneg (requestForm v z)).trans hform
  nlinarith [mul_nonneg hK (sub_nonneg.mpr hden)]

end Compression
end LinearProgramming
end Optimization
end OAI
