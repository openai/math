import OAI.LinearAlgebra.TensorSpectrum.GrowthRow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Model
import OAI.LinearAlgebra.MatrixExponent.Spectral.Placements
import OAI.LinearAlgebra.MatrixExponent.Spectral.Wire
import Mathlib.Algebra.BigOperators.Fin
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Bounds
import OAI.LinearAlgebra.MatrixExponent.Spectral.Transport
import OAI.LinearAlgebra.MatrixExponent.Spectrum.Extension
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Model
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import OAI.LinearAlgebra.MatrixExponent.FieldExtension
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Mask
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Ring.Shrink
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.SetTheory.Cardinal.Subfield

section
/-!
# Paired secant inequalities for polynomial multiplication

One application of tripling controls both rows at a common comparison
index. Concavity transports the bound back to *different* indices in
the two rows. The reciprocal inequality then controls a weighted sum
of logarithmic increments.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open OAI.LinearAlgebra.TensorSpectrum

/-- The indices are degrees, one less than the polynomial lengths. -/
structure Row (f g : ℕ → ℝ) (m : ℕ) : Prop where
  pos : ∀ n, 0 < f n
  dec : Antitone (rowDifference f)
  trip : ∀ n, 2 * f n + g n ≤ f (3 * n + m + 2)

variable {f g : ℕ → ℝ} {m n : ℕ}

private theorem Row.slope (h : Row f g m) (n : ℕ) :
    (f n + g n) / (2 * (n : ℝ) + m + 2) ≤ rowDifference f n := by
  have h₁ := (row_secant_bounds f h.dec n (2 * n + m + 2)).1
  rw [show n + (2 * n + m + 2) = 3 * n + m + 2 by omega] at h₁
  push_cast at h₁
  apply (div_le_iff₀ (by positivity)).mpr
  linarith [h.trip n]

private theorem Row.increase (h : Row f g m) {L : ℝ} (hL : L ≤ rowDifference f n)
    {j k : ℕ} (hk : j + k ≤ n) : f j + k * L ≤ f (j + k) := by
  refine le_trans ?_ (row_secant_bounds f h.dec j k).2
  gcongr
  exact hL.trans (h.dec hk)

private theorem log_increase {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (y - x) / y ≤ Real.log y - Real.log x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at h
  rw [sub_div, div_self hy.ne']
  linarith

/-- Lower bound on a pair of increments per unit increase of the index. -/
theorem paired_secants (hf : Row f g m) (hg : Row g f m) (j k b c : ℕ)
    (hb : 0 < b) (hc : 0 < c) :
    4 / (m + (j + b) + (k + c) + 2 : ℕ) ≤
      (Real.log (f (j + b)) - Real.log (f j)) / b +
      (Real.log (g (k + c)) - Real.log (g k)) / c := by
  let N := (j + b) + (k + c)
  let L := (f N + g N) / (2 * (N : ℝ) + m + 2)
  have hL : 0 < L := div_pos (add_pos (hf.pos _) (hg.pos _)) (by positivity)
  have hLf : L ≤ rowDifference f N := hf.slope N
  have hLg : L ≤ rowDifference g N := by
    rw [show L = (g N + f N) / (2 * (N : ℝ) + m + 2) by unfold L; rw [add_comm (g N)]]
    exact hg.slope N
  let X := f (j + b)
  let Y := g (k + c)
  have hX : 0 < X := hf.pos _
  have hY : 0 < Y := hg.pos _
  have hsum : X + Y ≤ (m + (j + b) + (k + c) + 2 : ℕ) * L := by
    have h₁ := hf.increase hLf (j := j + b) (k := k + c) le_rfl
    have h₂ := hg.increase hLg (j := k + c) (k := j + b) (by unfold N; omega)
    rw [add_comm (k + c)] at h₂
    have he : L * (2 * (N : ℝ) + m + 2) = f N + g N := div_mul_cancel₀ _ (by positivity)
    unfold N at he
    unfold X Y
    push_cast at *
    linarith
  have part {f g : ℕ → ℝ} (h : Row f g m) (hf' : L ≤ rowDifference f N)
      {j b : ℕ} (hb : 0 < b) (hN : j + b ≤ N) :
      L / f (j + b) ≤ (Real.log (f (j + b)) - Real.log (f j)) / b := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [div_mul_eq_mul_div]
    exact (div_le_div_of_nonneg_right (by linarith [h.increase hf' hN]) (h.pos _).le).trans
      (log_increase (h.pos j) (h.pos (j + b)))
  calc
    _ ≤ 4 * L / (X + Y) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      linarith
    _ ≤ L / X + L / Y := by
      field_simp
      nlinarith [sq_nonneg (X - Y)]
    _ ≤ _ := add_le_add (part hf hLf hb (by unfold N; omega))
      (part hg hLg hc (by unfold N; omega))

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-!
# The polar formula for the rectangular benchmark

The three arm lengths `x,y,z` give wire lengths `x+y,x+z,y+z`.
The dual inequality follows by weighted Cauchy–Schwarz. At an active
shape all three arms of a maximizing tripod can be strictly positive.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

def load (a b c x y z : ℝ) : ℝ := x * (a + b) + y * (a + c) + z * (b + c)

def dStar (x y z : ℝ) : ℝ := x + y + z - x * y * z / (x * y + y * z + z * x)

def area (a b c : ℝ) : ℝ := max (a + b) (max (a + c) (b + c))

variable {a b c x y z s t u : ℝ}

private theorem cauchy (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hs : s + t + u = 1) :
    x * y * z / (x * y + y * z + z * x) ≤ x * s ^ 2 + y * t ^ 2 + z * u ^ 2 := by
  rcases eq_or_lt_of_le (by positivity : 0 ≤ x * y + y * z + z * x) with h | h
  · rw [← h, div_zero]
    positivity
  apply (div_le_iff₀ h).2
  have h' : 0 ≤ z * (x * s - y * t) ^ 2 + y * (x * s - z * u) ^ 2 + x * (y * t - z * u) ^ 2 := by positivity
  calc
    _ = x * y * z * (s + t + u) ^ 2 := by rw [hs]; ring
    _ ≤ _ := by linarith only [h']

theorem dStar_pos (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 0 < dStar x y z := by
  have := cauchy hx.le hy.le hz.le (show (1 : ℝ) + 0 + 0 = 1 by norm_num)
  unfold dStar
  linarith

private theorem dStar_cycle (x y z : ℝ) : dStar z x y = dStar x y z := by
  unfold dStar
  ring

private theorem load_cycle (a b c x y z : ℝ) : load b c a z x y = load a b c x y z := by
  unfold load
  ring

private theorem area_cycle (a b c : ℝ) : area b c a = area a b c := by
  unfold area
  simp only [add_comm, max_comm, max_left_comm]

/-- The polar upper bound, with attainment at positive arms above the
largest pair sum. At or below that sum a single nonzero arm suffices. -/
structure Polar (a b c v : ℝ) : Prop where
  area_le : area a b c ≤ v
  bound : ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → load a b c x y z ≤ v * dStar x y z
  achieves : area a b c < v → ∃ x y z : ℝ,
    0 < x ∧ 0 < y ∧ 0 < z ∧ load a b c x y z = v * dStar x y z

private theorem Polar.rotate {v : ℝ} (h : Polar b c a v) : Polar a b c v := by
  refine ⟨(area_cycle a b c).symm.trans_le h.area_le, ?_, ?_⟩
  · intro x y z hx hy hz
    simpa only [load_cycle a b c, dStar_cycle x y z] using h.bound z x y hz hx hy
  · intro hlt
    obtain ⟨z, x, y, hz, hx, hy, he⟩ := h.achieves ((area_cycle a b c).trans_lt hlt)
    exact ⟨x, y, z, hx, hy, hz, by rwa [load_cycle a b c, dStar_cycle x y z] at he⟩

/-- Three weights adding to one certify an upper bound on the objective. -/
private theorem certificate {v : ℝ} (hv : 0 ≤ v) (hs : s + t + u = 1)
    (h₁ : a + b ≤ v * (1 - s ^ 2)) (h₂ : a + c ≤ v * (1 - t ^ 2))
    (h₃ : b + c ≤ v * (1 - u ^ 2)) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    load a b c x y z ≤ v * dStar x y z := by
  calc
    _ ≤ x * (v * (1 - s ^ 2)) + y * (v * (1 - t ^ 2)) + z * (v * (1 - u ^ 2)) := by
      unfold load
      gcongr
    _ = v * (x + y + z - (x * s ^ 2 + y * t ^ 2 + z * u ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_sub_left (cauchy hx hy hz hs) _) hv

private theorem optimizer {v : ℝ} (hs : 0 < s) (ht : 0 < t) (hu : 0 < u)
    (hsum : s + t + u = 1) (h₁ : a + b = v * (1 - s ^ 2))
    (h₂ : a + c = v * (1 - t ^ 2)) (h₃ : b + c = v * (1 - u ^ 2)) :
    load a b c s⁻¹ t⁻¹ u⁻¹ = v * dStar s⁻¹ t⁻¹ u⁻¹ := by
  have he : s⁻¹ * t⁻¹ * u⁻¹ / (s⁻¹ * t⁻¹ + t⁻¹ * u⁻¹ + u⁻¹ * s⁻¹) = 1 := by
    field_simp
    linarith
  rw [load, h₁, h₂, h₃, dStar, he]
  have hr (p : ℝ) (hp : 0 < p) : p⁻¹ * (v * (1 - p ^ 2)) = v * (p⁻¹ - p) := by field_simp
  rw [hr s hs, hr t ht, hr u hu, ← hsum]
  ring

private theorem polar_ordered (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hca : c ≤ a) (hcb : c ≤ b) : Polar a b c (benchmark a b c) := by
  have hM : area a b c = a + b := max_eq_left (max_le (by linarith) (by linarith))
  by_cases h : (a + b) * c ≤ a * b
  · have he : benchmark a b c = a + b := by simp [benchmark, max_eq_right (sub_nonpos.mpr h)]
    rw [he]
    refine ⟨hM.le, ?_, fun h' => (hM.ge.not_gt h').elim⟩
    intro x y z hx hy hz
    refine certificate (s := 0) (t := b / (a + b)) (u := a / (a + b))
      (by positivity) ?_ (by simp) ?_ ?_ hx hy hz
    · field_simp; ring
    · field_simp; nlinarith only [h]
    · field_simp; nlinarith only [h]
  · have h' : a * b < (a + b) * c := lt_of_not_ge h
    let K := a * b + a * c + b * c
    have hK : 0 < K := by unfold K; positivity
    let v := K ^ 2 / (4 * a * b * c)
    have hv : 0 < v := by unfold v; positivity
    have he : benchmark a b c = v := by
      rw [benchmark, max_eq_left (sub_nonneg.mpr h'.le)]
      unfold v K
      field_simp
      ring
    rw [he]
    let s := 1 - 2 * a * b / K
    let t := 1 - 2 * a * c / K
    let u := 1 - 2 * b * c / K
    have hs : 0 < s := sub_pos.mpr ((div_lt_one hK).2 (by unfold K; linarith))
    have ht : 0 < t := sub_pos.mpr ((div_lt_one hK).2 (by unfold K; nlinarith))
    have hu : 0 < u := sub_pos.mpr ((div_lt_one hK).2 (by unfold K; nlinarith))
    have hsum : s + t + u = 1 := by unfold s t u; field_simp; unfold K; ring
    have h₁ : a + b = v * (1 - s ^ 2) := by unfold v s; field_simp; unfold K; ring
    have h₂ : a + c = v * (1 - t ^ 2) := by unfold v t; field_simp; unfold K; ring
    have h₃ : b + c = v * (1 - u ^ 2) := by unfold v u; field_simp; unfold K; ring
    refine ⟨?_, fun _ _ _ => certificate hv.le hsum h₁.le h₂.le h₃.le, fun _ =>
      ⟨s⁻¹, t⁻¹, u⁻¹, by positivity, by positivity, by positivity,
        optimizer hs ht hu hsum h₁ h₂ h₃⟩⟩
    rw [hM, ← he, benchmark]
    exact le_add_of_nonneg_right (by positivity)

theorem polar (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : Polar a b c (U a b c) := by
  unfold U
  split_ifs with h h'
  · exact polar_ordered ha hb hc (le_min_iff.mp h).1 (le_min_iff.mp h).2
  · rw [min_eq_left h'] at h
    exact (polar_ordered hb hc ha h' (le_of_not_ge h)).rotate
  · rw [min_eq_right (le_of_not_ge h')] at h
    exact (polar_ordered hc ha hb (le_of_not_ge h) (le_of_not_ge h')).rotate.rotate

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-! # Three wires for a rectangular matrix product -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Spectral

/-- The output is at site 0, the two inputs at sites 1 and 2. -/
def tensor (K : Type) [Field K] (i j k : ℕ) : Tensor K (Fin 3) :=
  Tensor.wire K 0 1 i * Tensor.wire K 0 2 j * Tensor.wire K 1 2 k

theorem tensor_power (K : Type) [Field K] (i j k t : ℕ) :
    tensor K (i ^ t) (j ^ t) (k ^ t) = (tensor K i j k) ^ t := by
  induction t with
  | zero => simp [tensor, Tensor.wire, Tensor.shared_one]
  | succ t ih =>
    rw [pow_succ, pow_succ, pow_succ, pow_succ, ← ih]
    simp only [tensor, Tensor.wire, Tensor.shared_mul]
    exact (congrArg (· * _) (mul_mul_mul_comm _ _ _ _)).trans (mul_mul_mul_comm _ _ _ _)

variable {K L : Type} [Field K] [Field L]

theorem tensor_map (φ : K →+* L) (i j k : ℕ) :
    Tensor.map φ (tensor K i j k) = tensor L i j k := by
  have hw (a b : Fin 3) (n : ℕ) : Tensor.map φ (Tensor.wire K a b n) = Tensor.wire L a b n := by
    apply Tensor.ofRaw_eq
    refine Raw.relabel (Equiv.refl _) (fun _ => Equiv.refl _) fun i s x => ?_
    change Fin n at i x
    change φ (if x = Raw.port {a, b} s i then 1 else 0) =
      if x = Raw.port {a, b} s i then 1 else 0
    split <;> simp
  rw [tensor, tensor, map_mul, map_mul, hw, hw, hw]

abbrev rawWires (K : Type) [Field K] (i j k : ℕ) : Raw K (Fin 3) :=
  Raw.wire K 0 1 i * Raw.wire K 0 2 j * Raw.wire K 1 2 k

variable {i j k r : ℕ}

theorem coeff_wires (x : Fin 3 → (Fin i × Fin j) × Fin k) :
    (rawWires K i j k).coeff x =
      if (x 0).2.val = 0 ∧ (x 1).1.2.val = 0 ∧ (x 2).1.1.val = 0 then
        if (x 1).1.1 = (x 0).1.1 ∧ (x 1).2 = (x 2).2 ∧ (x 2).1.2 = (x 0).1.2 then 1 else 0
      else 0 := by
  change (∑ t : (Fin i × Fin j) × Fin k, ∏ s : Fin 3,
    ((if (x s).1.1 = Raw.port {0, 1} s t.1.1 then 1 else 0) *
      (if (x s).1.2 = Raw.port {0, 2} s t.1.2 then 1 else 0) *
      (if (x s).2 = Raw.port {1, 2} s t.2 then 1 else 0) : K)) = _
  rw [Fintype.sum_eq_single ((x 0).1, (x 1).2)]
  · simp [Fin.prod_univ_three, Raw.port]
    simp only [Fin.ext_iff]
    grind
  · intro t ht
    simp [Fin.prod_univ_three, Raw.port]
    grind

/-- Restriction from a diagonal is exactly a coefficient decomposition.
Each site in the three-wire model has one unused index fixed to zero. -/
theorem tensor_le_iff (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    tensor K i j k ≤ (r : Tensor K (Fin 3)) ↔ RankLE K i j k r := by
  rw [← Tensor.diag_fin]
  change (∃ A : Fin 3 → (Fin i × Fin j) × Fin k → Fin r → K,
    ∀ x : Fin 3 → (Fin i × Fin j) × Fin k,
      (rawWires K i j k).coeff x =
        ∑ l : Fin r, ∏ s, ∑ y : Fin r, A s (x s) y * if y = l then 1 else 0) ↔ _
  simp only [mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq', Fin.prod_univ_three, coeff_wires]
  constructor
  · rintro ⟨A, hA⟩
    let X (x : Pos i k) := ((x.1, (⟨0, hj⟩ : Fin j)), x.2)
    let Y (y : Pos k j) := (((⟨0, hi⟩ : Fin i), y.2), y.1)
    let Z (z : Pos i j) := (z, (⟨0, hk⟩ : Fin k))
    refine ⟨fun l x => A 1 (X x) l, fun l y => A 2 (Y y) l, fun l z => A 0 (Z z) l, ?_⟩
    intro x y z
    have ha := (hA ![Z z, X x, Y y]).symm
    simp [X, Y, Z, mul_assoc, mul_comm] at ha ⊢
    exact ha
  · rintro ⟨a, b, c, h⟩
    refine ⟨![fun p l => if p.2.val = 0 then c l p.1 else 0,
      fun p l => if p.1.2.val = 0 then a l (p.1.1, p.2) else 0,
      fun p l => if p.1.1.val = 0 then b l (p.2, p.1.2) else 0], ?_⟩
    intro x
    by_cases h₀ : (x 0).2.val = 0
    swap; · simp [h₀]
    by_cases h₁ : (x 1).1.2.val = 0
    swap; · simp [h₁]
    by_cases h₂ : (x 2).1.1.val = 0
    swap; · simp [h₂]
    simpa [h₀, h₁, h₂, mul_assoc, mul_comm, mul_left_comm] using
      (h ((x 1).1.1, (x 1).2) ((x 2).2, (x 2).1.2) (x 0).1).symm

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
# Positive spectral contact implies rectangular rigidity

The normalized price triples are arm lengths at diagonal rate one.
The two geometric inputs are the harmonic lower bound on the rate
and propagation from a positive triple attaining that lower bound.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {P : ℝ → ℝ → ℝ → Prop}

/-- A support representation by nonnegative normalized arms. -/
structure Support (F : Type*) [Field F] (P : ℝ → ℝ → ℝ → Prop) : Prop where
  nonneg : ∀ {x y z}, P x y z → 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z
  bound : ∀ {a b c x y z}, 0 ≤ a → 0 ≤ b → 0 ≤ c → P x y z →
    load a b c x y z ≤ exponent F a b c
  attains : ∀ {a b c}, 0 ≤ a → 0 ≤ b → 0 ≤ c →
    ∃ x y z, P x y z ∧ load a b c x y z = exponent F a b c

def DiagonalBound (P : ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ x y z, P x y z → dStar x y z ≤ 1

def Propagation (P : ℝ → ℝ → ℝ → Prop) : Prop :=
  (∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ P x y z ∧ dStar x y z = 1) →
  ∀ x y z, 0 < x → 0 < y → 0 < z →
    P (x / dStar x y z) (y / dStar x y z) (z / dStar x y z)

private theorem boundary {a b c x y z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : dStar x y z ≤ 1) (h' : x = 0 ∨ y = 0 ∨ z = 0) :
    load a b c x y z ≤ area a b c := by
  have hsum : x + y + z ≤ 1 := by
    rcases h' with h' | h' | h' <;> simpa [dStar, h'] using h
  let M := area a b c
  have h₁ : a + b ≤ M := le_max_left _ _
  have h₂ : a + c ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : b + c ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  calc
    _ ≤ x * M + y * M + z * M := by unfold load; gcongr
    _ = (x + y + z) * M := by ring
    _ ≤ M := mul_le_of_le_one_left (by linarith) hsum

theorem upper_of_diagonal (hs : Support F P) (hd : DiagonalBound P)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    exponent F a b c ≤ U a b c := by
  have h := polar ha hb hc
  have hU : 0 ≤ U a b c := (add_pos ha hb).le.trans ((le_max_left _ _).trans h.area_le)
  obtain ⟨x, y, z, hP, he⟩ := hs.attains ha.le hb.le hc.le
  obtain ⟨hx, hy, hz⟩ := hs.nonneg hP
  exact he.ge.trans ((h.bound _ _ _ hx hy hz).trans
    (mul_le_of_le_one_right hU (hd x y z hP)))

theorem rigidity_of_contact (hs : Support F P) (hd : DiagonalBound P)
    (hp : Propagation P) : Rigidity F := by
  by_cases ht : ∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ P x y z ∧ dStar x y z = 1
  · left
    intro a b c ha hb hc
    refine le_antisymm (upper_of_diagonal hs hd ha hb hc) ?_
    by_cases h : area a b c < U a b c
    · obtain ⟨x, y, z, hx, hy, hz, he⟩ := (polar ha hb hc).achieves h
      have hh := hs.bound ha.le hb.le hc.le (hp ht x y z hx hy hz)
      let D := dStar x y z
      have hD : 0 < D := dStar_pos hx hy hz
      calc
        U a b c = load a b c x y z / D := (eq_div_iff hD.ne').2 he.symm
        _ = load a b c (x / D) (y / D) (z / D) := by unfold load; ring
        _ ≤ _ := hh
    · exact (le_of_not_gt h).trans (bounds F ha.le hb.le hc.le).1
  · right
    intro a b c ha hb hc hactive
    obtain ⟨x, y, z, hP, he⟩ := hs.attains ha.le hb.le hc.le
    obtain ⟨hx, hy, hz⟩ := hs.nonneg hP
    have hD := hd x y z hP
    rw [← he]
    by_cases h' : x = 0 ∨ y = 0 ∨ z = 0
    · exact (boundary ha hb hx hy hz hD h').trans_lt hactive
    push Not at h'
    have hD' : dStar x y z < 1 := lt_of_le_of_ne hD fun he =>
      ht ⟨x, y, z, hx.lt_of_ne' h'.1, hy.lt_of_ne' h'.2.1, hz.lt_of_ne' h'.2.2, hP, he⟩
    exact ((polar ha hb hc).bound _ _ _ hx hy hz).trans_lt
      (mul_lt_of_lt_one_right ((add_pos ha hb).trans_le (le_max_left _ _) |>.trans hactive) hD')

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-! # Three-site spectral points and normalized prices -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Spectral
open scoped NNReal

variable {F : Type} [Field F]

abbrev Point (F : Type) [Field F] := Tensor F (Fin 3) →+* ℝ≥0

def dist (f : Point F) : Fin 3 → Fin 3 → ℝ := Tensor.dist (NNReal.toRealHom.comp f)

def score (f : Point F) (a b c : ℝ) : ℝ :=
  a * dist f 0 1 + b * dist f 0 2 + c * dist f 1 2

def Prices (F : Type) [Field F] (x y z : ℝ) : Prop :=
  ∃ f : Point F, Monotone f ∧ dist f 0 1 = x + y ∧ dist f 0 2 = x + z ∧ dist f 1 2 = y + z

variable {f : Point F} {x y z a b c : ℝ}

theorem mono_real (hf : Monotone f) : Monotone (NNReal.toRealHom.comp f) :=
  fun _ _ h => NNReal.coe_le_coe.mpr (hf h)

theorem dist_bounds (hf : Monotone f) (i j : Fin 3) : 0 ≤ dist f i j ∧ dist f i j ≤ 1 :=
  ⟨Tensor.dist_nonneg _ (mono_real hf) i j, Tensor.dist_le_one _ (mono_real hf) i j⟩

theorem Prices.nonneg (h : Prices F x y z) : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z := by
  obtain ⟨f, hf, h₁, h₂, h₃⟩ := h
  have tri (i j k : Fin 3) : dist f i k ≤ dist f i j + dist f j k :=
    Tensor.dist_triangle _ (mono_real hf) i j k
  have comm (i j : Fin 3) : dist f i j = dist f j i := Tensor.dist_comm _ i j
  refine ⟨?_, ?_, ?_⟩
  · linarith [tri 1 0 2, comm 1 0]
  · linarith [tri 0 1 2]
  · linarith [tri 0 2 1, comm 2 1]

theorem Prices.score (h : Prices F x y z) :
    ∃ f : Point F, Monotone f ∧ load a b c x y z = score f a b c := by
  obtain ⟨f, hf, h₁, h₂, h₃⟩ := h
  refine ⟨f, hf, ?_⟩
  rw [Rectangle.score, load, h₁, h₂, h₃]
  ring

theorem score_eq_load (hf : Monotone f) :
    ∃ x y z, Prices F x y z ∧ load a b c x y z = score f a b c := by
  let p := (dist f 0 1 + dist f 0 2 + dist f 1 2) / 2
  refine ⟨p - dist f 1 2, p - dist f 0 2, p - dist f 0 1, ⟨f, hf, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp only [p, load, score]; ring

private theorem nonempty_points (F : Type) [Field F] :
    (Spectrum.points (Tensor F (Fin 3))).Nonempty := by
  obtain ⟨f, hf, _⟩ := Spectrum.extension Tensor.add_le_add_right Tensor.mul_le_mul_left
    Tensor.zero_le Tensor.one_le Tensor.exists_bound (Nat.castRingHom (Tensor F (Fin 3)))
    (Nat.castRingHom ℝ≥0) (fun m n h => Nat.cast_le.mpr ((Tensor.natCast_le_iff m n).mp h))
  exact ⟨f, f, hf, rfl⟩

theorem maximum_score (F : Type) [Field F] (a b c : ℝ) :
    ∃ f : Point F, Monotone f ∧ ∀ g : Point F, Monotone g → score g a b c ≤ score f a b c := by
  let P := Spectrum.points (Tensor F (Fin 3))
  let d (i j : Fin 3) (g : Tensor F (Fin 3) → ℝ≥0) :=
    Real.log (g (Tensor.wire F i j 2)) / Real.log 2
  have hd (i j : Fin 3) : ContinuousOn (d i j) P := by
    apply ContinuousOn.div_const
    have hc : Continuous (fun g : Tensor F (Fin 3) → ℝ≥0 => (g (Tensor.wire F i j 2) : ℝ)) := by fun_prop
    apply ContinuousOn.log hc.continuousOn
    rintro _ ⟨g, hg, rfl⟩
    have h : 1 ≤ g (Tensor.wire F i j 2) := by
      simpa using hg (Tensor.one_le_wire F i j (n := 2) (by decide))
    exact ne_of_gt (show (0 : ℝ) < g (Tensor.wire F i j 2) by positivity)
  have ht : ContinuousOn (fun g => a * d 0 1 g + b * d 0 2 g + c * d 1 2 g) P :=
    (((hd 0 1).const_mul a).add ((hd 0 2).const_mul b)).add ((hd 1 2).const_mul c)
  obtain ⟨_, ⟨f, hf, rfl⟩, h⟩ :=
    (Spectrum.compact_points Tensor.exists_bound).exists_isMaxOn (nonempty_points F) ht
  exact ⟨f, hf, fun g hg => h ⟨g, hg, rfl⟩⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
# Powers of a point in the Zariski closure

Polynomial evaluation carries a closure point into the linear span of
the evaluations on the original set. The degree-`n` products only use
monomials with each exponent at most `n`, giving a polynomial bound on
the number of points needed in one simultaneous interpolation.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Finset

variable {F : Type*} [Field F] {ι : Type}

variable {s : Set (ι → F)} {x : ι → F}

private theorem ZClosure.evaluate (h : ZClosure s x) {κ : Type} [Fintype κ]
    (p : κ → MvPolynomial ι F) :
    ∃ d : ℕ, d ≤ Fintype.card κ ∧ ∃ (y : Fin d → ι → F) (c : Fin d → F),
      (∀ t, y t ∈ s) ∧ ∀ i, MvPolynomial.eval x (p i) = ∑ t, c t * MvPolynomial.eval (y t) (p i) := by
  classical
  let v (z : ι → F) i := MvPolynomial.eval z (p i)
  let W := Submodule.span F (v '' s)
  have hx : v x ∈ W := by
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp
    intro φ hφ
    let q := ∑ i, MvPolynomial.C (φ (Pi.basisFun F κ i)) * p i
    have eqn (z : ι → F) : φ (v z) = MvPolynomial.eval z q := by
      rw [← (Pi.basisFun F κ).sum_repr (v z), map_sum]
      simp only [map_smul, Pi.basisFun_repr, smul_eq_mul, q, map_sum, map_mul, MvPolynomial.eval_C,
        v, mul_comm]
    rw [eqn]
    apply h
    intro z hz
    rw [← eqn]
    exact (Submodule.mem_dualAnnihilator φ).mp hφ _ (Submodule.subset_span ⟨z, hz, rfl⟩)
  obtain ⟨b, hb, he, _⟩ := Submodule.exists_fun_fin_finrank_span_eq F (v '' s)
  choose y hy hy' using hb
  have hx' : v x ∈ Submodule.span F (Set.range b) := he.symm ▸ hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hx'
  refine ⟨Module.finrank F W, ?_, y, c, hy, fun i => ?_⟩
  · simpa using W.finrank_le
  · simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hy', v] using congrFun hc.symm i

theorem ZClosure.power [Fintype ι] (h : ZClosure s x) (n : ℕ) :
    ∃ d : ℕ, d ≤ (n + 1) ^ Fintype.card ι ∧ ∃ (y : Fin d → ι → F) (c : Fin d → F),
      (∀ t, y t ∈ s) ∧ ∀ f : Fin n → ι, ∏ l, x (f l) = ∑ t, c t * ∏ l, y t (f l) := by
  classical
  let p (e : ι → Fin (n + 1)) : MvPolynomial ι F := ∏ i, MvPolynomial.X i ^ (e i).val
  obtain ⟨d, hd, y, c, hy, hc⟩ := h.evaluate p
  refine ⟨d, by simpa using hd, y, c, hy, fun f => ?_⟩
  let e (i : ι) : Fin (n + 1) := ⟨(univ.filter (fun l => f l = i)).card,
    Nat.lt_succ_of_le (by simpa using card_filter_le univ (fun l => f l = i))⟩
  have he (z : ι → F) : MvPolynomial.eval z (p e) = ∏ l, z (f l) := by
    rw [← prod_fiberwise' univ f z]
    simp only [p, map_prod, map_pow, MvPolynomial.eval_X, prod_const, e]
  simpa only [he] using hc e

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
# Scalar extension for the density bound

The weights and a rank witness lie in one countable subfield. Both embeddings
from that subfield preserve all coefficient equations and the set of nonzero
weights. The unweighted arithmetic exponent is invariant under extension.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F K : Type*} [Field F] [Field K] {i j k r : ℕ} {w : Fin i → Fin j → Fin k → F}

theorem WeightedRankLE.map (h : WeightedRankLE w r) (φ : F →+* K) :
    WeightedRankLE (fun x y z => φ (w x y z)) r := by
  obtain ⟨a, b, c, h⟩ := h
  refine ⟨fun l x => φ (a l x), fun l y => φ (b l y), fun l z => φ (c l z), ?_⟩
  intro x y z
  simpa only [map_sum, map_mul, apply_ite φ, map_zero] using congrArg φ (h x y z)

theorem supportSize_map (φ : F →+* K) (w : Fin i → Fin j → Fin k → F) :
    supportSize (fun x y z => φ (w x y z)) = supportSize w := by
  classical
  have he (x : F) : φ x = 0 ↔ x = 0 := by rw [← map_zero φ, φ.injective.eq_iff]
  simp only [supportSize, he]

theorem small_coefficients {ι : Type} [Countable ι] (v : ι → F) :
    ∃ (L : Type) (_ : Field L) (φ : L →+* F) (u : ι → L), ∀ t, φ (u t) = v t := by
  let H := Subfield.closure (Set.range v)
  have : Countable H := Cardinal.mk_le_aleph0_iff.mp
    ((Subfield.cardinalMk_closure_le_max (Set.range v)).trans
      (max_le (Cardinal.le_aleph0_iff_set_countable.mpr (Set.countable_range v)) le_rfl))
  let e : Shrink.{0} H ≃+* H := Shrink.ringEquiv.{0} H
  exact ⟨Shrink.{0} H, inferInstance, H.subtype.comp e.toRingHom,
    fun t => e.symm ⟨v t, Subfield.subset_closure ⟨t, rfl⟩⟩, by simp⟩

theorem small_witness (h : WeightedRankLE w r) :
    ∃ (L : Type) (_ : Field L) (φ : L →+* F) (v : Fin i → Fin j → Fin k → L),
      WeightedRankLE v r ∧ (fun x y z => φ (v x y z)) = w := by
  obtain ⟨a, b, c, hc⟩ := h
  let data : (Fin i × Fin j × Fin k) ⊕ (Fin r × (Pos i k ⊕ Pos k j ⊕ Pos i j)) → F :=
    Sum.elim (fun p => w p.1 p.2.1 p.2.2) (fun p => Sum.elim (a p.1) (Sum.elim (b p.1) (c p.1)) p.2)
  obtain ⟨L, _, φ, u, hu⟩ := small_coefficients data
  refine ⟨L, inferInstance, φ, fun x y z => u (.inl (x, y, z)), ?_, funext fun x =>
    funext fun y => funext fun z => hu (.inl (x, y, z))⟩
  refine ⟨fun l x => u (.inr (l, .inl x)), fun l y => u (.inr (l, .inr (.inl y))),
    fun l z => u (.inr (l, .inr (.inr z))), fun x y z => ?_⟩
  apply φ.injective
  simp only [map_sum, map_mul, apply_ite φ, map_zero, hu]
  exact hc x y z

theorem density_of_closed (h : ∀ (K : Type) [Field K] [IsAlgClosed K], DensityBound K)
    (F : Type*) [Field F] : DensityBound F := by
  intro i j k r hi hj hk w hw
  obtain ⟨L, _, φ, v, hv, he⟩ := small_witness hw
  let : Algebra L F := φ.toAlgebra
  have h' := h (AlgebraicClosure L) i j k r hi hj hk _ (hv.map (algebraMap L (AlgebraicClosure L)))
  have ha : 0 ≤ Real.log i := Real.log_nonneg (by exact_mod_cast hi)
  have hb : 0 ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj)
  have hc : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  rw [← he, supportSize_map, exponent_extension L F ha hb hc]
  rwa [supportSize_map, exponent_extension L (AlgebraicClosure L) ha hb hc] at h'

theorem cells_of_closed (h : ∀ (K : Type) [Field K] [IsAlgClosed K], CellBound K)
    (F : Type*) [Field F] : CellBound F := by
  intro i j k r hi hj hk w u hu hw hr
  obtain ⟨L, _, φ, v, hv, he⟩ := small_witness hr
  let : Algebra L F := φ.toAlgebra
  let ψ := algebraMap L (AlgebraicClosure L)
  have he' (x y z) : ψ (v x y z) ≠ 0 ↔ (x, y) ∈ u := by
    rw [← hw x y z, ← he]
    simp
  have h' := h (AlgebraicClosure L) i j k r hi hj hk _ u hu he' (hv.map ψ)
  obtain ⟨ha, hb⟩ := short_bounds hi hj hu.card_pos
  have hc : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  rw [exponent_extension L F ha (sub_nonneg.mpr hb) hc]
  rwa [exponent_extension L (AlgebraicClosure L) ha (sub_nonneg.mpr hb) hc] at h'

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end
