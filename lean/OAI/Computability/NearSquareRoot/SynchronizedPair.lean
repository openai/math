import OAI.Computability.NearSquareRoot.SynchronizedPairBounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! # Synchronizing two-coordinate unitaries with Walsh rounds

These are the local pair layers in the synchronized short Fourier transform.
The three occurrences of the normalized Walsh matrix have identical positions
for every pair. The table data between them are diagonal phases.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedPair

open ComplexConjugate

noncomputable section

abbrev PairMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Component of a normalized two-point Walsh transform. -/
def w : ℝ := (Real.sqrt 2)⁻¹

def walsh : PairMatrix := !![(w : ℂ), w; w, -(w : ℂ)]

def pair (z : ℂ) : PairMatrix :=
  let t : ℝ := Real.sqrt (1 - ‖z‖ ^ 2)
  !![z, (t : ℂ); t, -conj z]

def diag (a b : ℂ) : PairMatrix := !![a, 0; 0, b]

private theorem w_sq : 2 * (w : ℂ) ^ 2 = 1 := by
  have h : 2 * w ^ 2 = 1 := by
    rw [w, inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  exact_mod_cast h

theorem walsh_sq : walsh * walsh = 1 := by
  rw [walsh, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination w_sq

private theorem mix (c s : ℂ) :
    walsh * diag (c + Complex.I * s) (c - Complex.I * s) * walsh =
      !![c, Complex.I * s; Complex.I * s, c] := by
  simp only [walsh, diag, Matrix.mul_fin_two, mul_zero, add_zero, zero_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first | linear_combination c * w_sq | linear_combination Complex.I * s * w_sq

/-- An aligned pair can use a single fixed three-Walsh template with six
unit-modulus diagonal coefficients. -/
def ThreeWalsh (M : PairMatrix) : Prop :=
  ∃ a b c d e f : ℂ,
    ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ ‖c‖ = 1 ∧ ‖d‖ = 1 ∧ ‖e‖ = 1 ∧ ‖f‖ = 1 ∧
    M = walsh * diag a b * walsh * diag c d * walsh * diag e f

private theorem phase_norm (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    ‖(r : ℂ) + Complex.I * (s : ℂ)‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  simpa [pow_two] using hrs

def phase (a : ℂ) : ℂ := a / (‖a‖ : ℂ)

/-- The two outer, two middle, and two inner diagonal entries in the common
three-Walsh template. Each quotient normalizes one input to unit magnitude. -/
def tableEntry (a b : ℂ) : Fin 6 → ℂ :=
  let r : ℂ := ‖a‖
  let s : ℂ := ‖b‖
  let u := phase a
  let v := phase b
  ![u, Complex.I * conj v, r + Complex.I * s, r - Complex.I * s, 1,
    -Complex.I * conj u * v]

private theorem norm_phase {a : ℂ} (ha : 0 < ‖a‖) : ‖phase a‖ = 1 := by
  rw [phase, norm_div, Complex.norm_of_nonneg ha.le, div_self ha.ne']

private theorem scale_phase (a : ℂ) (ha : 0 < ‖a‖) : (‖a‖ : ℂ) * phase a = a := by
  unfold phase
  field_simp [show (‖a‖ : ℂ) ≠ 0 by exact_mod_cast ha.ne']

private theorem phase_cancel {a : ℂ} (ha : ‖a‖ = 1) : a * conj a = 1 := by
  rw [Complex.mul_conj', ha]
  norm_num

theorem factor_eq_table {a b : ℂ} (ha : 0 < ‖a‖) (hb : 0 < ‖b‖)
    (hs : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    let e := tableEntry a b
    (∀ i, ‖e i‖ = 1) ∧ !![a, b; -conj b, conj a] =
      diag (e 0) (e 1) * walsh * diag (e 2) (e 3) * walsh * diag (e 4) (e 5) := by
  let r : ℂ := ‖a‖
  let s : ℂ := ‖b‖
  let u := phase a
  let v := phase b
  have hu : ‖u‖ = 1 := norm_phase ha
  have hv : ‖v‖ = 1 := norm_phase hb
  have hra : r * u = a := scale_phase a ha
  have hsb : s * v = b := scale_phase b hb
  have h1 : u * conj u = 1 := phase_cancel hu
  have h2 : v * conj v = 1 := phase_cancel hv
  let I := Complex.I
  constructor
  · intro i
    fin_cases i
    · exact hu
    · change ‖I * conj v‖ = 1
      simp [I, hv]
    · exact phase_norm _ _ hs
    · change ‖r - I * s‖ = 1
      have h := phase_norm ‖a‖ (-‖b‖) (by simpa using hs)
      simpa [r, s, I, sub_eq_add_neg] using h
    · exact norm_one
    · change ‖-I * conj u * v‖ = 1
      simp [I, hu, hv]
  · change !![a, b; -conj b, conj a] = diag u (I * conj v) * walsh *
        diag (r + I * s) (r - I * s) * walsh * diag 1 (-I * conj u * v)
    rw [show diag u (I * conj v) * walsh * diag (r + I * s) (r - I * s) * walsh =
        diag u (I * conj v) * (walsh * diag (r + I * s) (r - I * s) * walsh) by
          simp only [Matrix.mul_assoc], mix]
    rw [← hra, ← hsb]
    simp only [map_mul, diag, Matrix.mul_fin_two, zero_mul, mul_zero, add_zero, zero_add,
      mul_one]
    have hr : conj r = r := Complex.conj_ofReal _
    have ht : conj s = s := Complex.conj_ofReal _
    rw [hr, ht]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [I] <;> ring_nf <;> try rw [Complex.I_sq]
    all_goals
      first | linear_combination s * v * h1 | linear_combination -(s * v) * h1 |
              linear_combination r * conj u * h2 | linear_combination -(r * conj u) * h2 | ring

private theorem assemble {M : PairMatrix} {a b g : ℂ} (ha : 0 < ‖a‖) (hb : 0 < ‖b‖)
    (hs : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (hg : ‖g‖ = 1)
    (hM : walsh * M = diag 1 g * !![a, b; -conj b, conj a]) : ThreeWalsh M := by
  let e := tableEntry a b
  obtain ⟨he, hQ⟩ := factor_eq_table ha hb hs
  refine ⟨e 0, g * e 1, e 2, e 3, e 4, e 5, he 0, ?_, he 2, he 3, he 4, he 5, ?_⟩
  · rw [norm_mul, hg, he 1, one_mul]
  have hg' : diag 1 g * diag (e 0) (e 1) = diag (e 0) (g * e 1) := by
    simp [diag]
  calc
    M = walsh * (walsh * M) := by rw [← Matrix.mul_assoc, walsh_sq, Matrix.one_mul]
    _ = _ := by
      rw [hM, hQ, ← hg']
      simp only [Matrix.mul_assoc, e]

/-- An unselected pair consumes the same three Walsh rounds as an active pair. -/
theorem identity_threeWalsh : ThreeWalsh 1 := by
  have hw : 0 < w := by unfold w; positivity
  have hn : ‖(w : ℂ)‖ = w := Complex.norm_of_nonneg hw.le
  have hs : 2 * w ^ 2 = 1 := by exact_mod_cast w_sq
  apply assemble (a := (w : ℂ)) (b := (w : ℂ)) (g := -1) (by rwa [hn]) (by rwa [hn])
  · rw [hn]
    linarith
  · simp
  · simp [walsh, diag]

/-- A required Walsh butterfly also fits the three-round pattern. -/
theorem walsh_threeWalsh : ThreeWalsh walsh := by
  refine ⟨1, 1, 1, 1, 1, 1, norm_one, norm_one, norm_one, norm_one, norm_one, norm_one, ?_⟩
  rw [show diag 1 1 = 1 from Matrix.one_fin_two.symm]
  simp only [Matrix.mul_one, walsh_sq, Matrix.one_mul]

private theorem pair_formula (z : ℂ) :
    let t : ℂ := (Real.sqrt (1 - ‖z‖ ^ 2) : ℝ)
    let a := (w : ℂ) * (z + t)
    let b := (w : ℂ) * (t - conj z)
    walsh * pair z = diag 1 1 * !![a, b; -conj b, conj a] := by
  dsimp only
  simp only [pair, walsh, diag, Matrix.mul_fin_two, Complex.conj_ofReal, map_mul, map_sub,
    map_add, zero_mul, one_mul, add_zero, zero_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Applying the explicit phase tables and the three unconditional Walsh rounds
recovers the chirp dilation pair. -/
theorem pair_eq_table {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    let t : ℂ := (Real.sqrt (1 - ‖z‖ ^ 2) : ℝ)
    let a := (w : ℂ) * (z + t)
    let b := (w : ℂ) * (t - conj z)
    let e := tableEntry a b
    (∀ i, ‖e i‖ = 1) ∧ pair z =
      walsh * diag (e 0) (e 1) * walsh * diag (e 2) (e 3) * walsh * diag (e 4) (e 5) := by
  obtain ⟨ha, hb, hab⟩ := synchronizedPair_bounds z hz
  let t : ℂ := (Real.sqrt (1 - ‖z‖ ^ 2) : ℝ)
  let a := (w : ℂ) * (z + t)
  let b := (w : ℂ) * (t - conj z)
  obtain ⟨he, hQ⟩ := factor_eq_table (a := a) (b := b) (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 5) ha)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 5) hb) hab
  refine ⟨he, ?_⟩
  have hf := pair_formula z
  change walsh * pair z = diag 1 1 * !![a, b; -conj b, conj a] at hf
  rw [show diag 1 1 = 1 from Matrix.one_fin_two.symm, Matrix.one_mul, hQ] at hf
  calc
    pair z = walsh * (walsh * pair z) := by rw [← Matrix.mul_assoc, walsh_sq, Matrix.one_mul]
    _ = _ := by rw [hf]; simp only [Matrix.mul_assoc, a, b, t]

/-- Every dilation pair whose multiplier has modulus at most one half can be
synchronized. The only divisions in the construction of the outer phases are
by the norms bounded in `synchronizedPair_bounds`. -/
theorem pair_threeWalsh {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ThreeWalsh (pair z) := by
  obtain ⟨he, hM⟩ := pair_eq_table hz
  exact ⟨_, _, _, _, _, _, he 0, he 1, he 2, he 3, he 4, he 5, hM⟩

/-- Adjoining the pair conjugates the chirp multiplier, preserving the template. -/
theorem adjoint_pair_threeWalsh {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ThreeWalsh (pair z).conjTranspose := by
  have h : (pair z).conjTranspose = pair (conj z) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pair, Matrix.conjTranspose_apply]
  rw [h]
  exact pair_threeWalsh (by simpa using hz)

end
end SynchronizedPair

end NearSquareRoot
end Computability
end OAI
