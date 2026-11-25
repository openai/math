import OAI.LinearAlgebra.SpectralBooks.ArithmeticExponent
import OAI.LinearAlgebra.SpectralBooks.Book
import OAI.LinearAlgebra.SpectralBooks.BorderComparison
import OAI.LinearAlgebra.SpectralBooks.SpectralPoint
import OAI.LinearAlgebra.SpectralBooks.WireProduct

/-! # The finite rank theorem from a spectral book

The input to the reduction is price data on the *metric* book. It consists
of a monotone, intersecting-submodular diagonal price, the half-perimeter upper bound for each page triangle, and normalized tensor
evaluations pricing the three wires by their lengths. Constructing these
data over a field is the geometric part of the manuscript.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open MatrixMultiplication.Foundation
open scoped NNReal

section

/-- The wire evaluations of a spectral point in a placement of three sites.
The factor `d` is the price of the common binary diagonal at the three sites. -/
structure PlacedWires (F : Type*) [Field F] {X : Type*} [PseudoMetricSpace X]
    (p : Fin 3 → X) (d : ℝ) where
  point : RankFunctional F
  nonneg : 0 ≤ d
  price12 (n : ℕ) (hn : 0 < n) :
    d * Real.logb 2 (point.value (wire12 F n)) = dist (p 0) (p 1) * Real.logb 2 n
  price23 (n : ℕ) (hn : 0 < n) :
    d * Real.logb 2 (point.value (wire23 F n)) = dist (p 1) (p 2) * Real.logb 2 n
  price31 (n : ℕ) (hn : 0 < n) :
    d * Real.logb 2 (point.value (wire31 F n)) = dist (p 2) (p 0) * Real.logb 2 n

/-- Multiplying the wires and comparing their evaluation to asymptotic
rank gives the rank bound at any placement. -/
theorem PlacedWires.wireSum_le {F : Type*} [Field F] {X : Type*} [PseudoMetricSpace X]
    {p : Fin 3 → X} {d : ℝ} (w : PlacedWires F p d)
    {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    dist (p 0) (p 1) * Real.logb 2 x + dist (p 1) (p 2) * Real.logb 2 y +
        dist (p 2) (p 0) * Real.logb 2 z ≤
      d * Real.logb 2 (asymptoticRank (matrixTensor F x y z)) := by
  let φ := w.point
  let T := matrixTensor F x y z
  have e : φ.value T = φ.value (wire12 F x) * φ.value (wire23 F y) * φ.value (wire31 F z) := by
    dsimp only [T]
    rw [matrixTensor_eq_wireProduct, φ.pullback_equiv, φ.product, φ.product]
  have hreal {a : ℝ≥0} (h : 1 ≤ a) : 0 < (a : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one h)
  have h12 : 0 < (φ.value (wire12 F x) : ℝ) := hreal (φ.one_le_of_entry_one
    (x := (⟨0,hx⟩ : Fin x)) (y := ⟨0,hx⟩) (z := ()) (by simp [wire12]))
  have h23 : 0 < (φ.value (wire23 F y) : ℝ) := hreal (φ.one_le_of_entry_one
    (x := ()) (y := (⟨0,hy⟩ : Fin y)) (z := ⟨0,hy⟩) (by simp [wire23]))
  have h31 : 0 < (φ.value (wire31 F z) : ℝ) := hreal (φ.one_le_of_entry_one
    (x := (⟨0,hz⟩ : Fin z)) (y := ()) (z := ⟨0,hz⟩) (by simp [wire31]))
  have hT : 0 < (φ.value T : ℝ) := by rw [e]; push_cast; positivity
  have h := mul_le_mul_of_nonneg_left
    (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hT (φ.le_asymptoticRank T)) w.nonneg
  rw [e, NNReal.coe_mul, NNReal.coe_mul, Real.logb_mul (mul_pos h12 h23).ne' h31.ne',
    Real.logb_mul h12.ne' h23.ne', mul_add, mul_add] at h
  exact (show _ from (w.price12 x hx ▸ w.price23 y hy ▸ w.price31 z hz ▸ h))

/-- The geometric data used from the spectral book and its pages in the
finite rectangular theorem. The quantified evaluations act on tensors over
the specified ground field. -/
structure PlanarBookPrices (F : Type*) [Field F] where
  diagonal : Finset (Book ℝ) → ℝ
  monotone : Monotone diagonal
  submodular : IntersectingSubmodular diagonal
  base : diagonal bookBase = 2
  triangle (r : Fin 3 → ℝ≥0) (i : Fin 3) : diagonal (insert (bookTip r i) bookBase) ≤
    (dist (bookSpine (-1)) (bookSpine 1) + dist (bookSpine 1) (bookTip r i) +
      dist (bookTip r i) (bookSpine (-1))) / 2
  wires (r : Fin 3 → ℝ≥0) (hr : ∀ i, 0 < r i) :
    PlacedWires F (bookTip r) (diagonal (Finset.univ.image (bookTip r)))

variable {F : Type*} [Field F]

/-- Inequality (height-bound) for the actual asymptotic tensor rank. -/
theorem PlanarBookPrices.heightTest (B : PlanarBookPrices F) {x y z : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    HeightTest (loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z))
      (Real.logb 2 (asymptoticRank (matrixTensor F x y z))) := by
  classical
  intro a ha
  let r (i : Fin 3) : ℝ≥0 := ⟨a i, (ha i).le⟩
  let w := B.wires r (fun i => ha i)
  have h := w.wireSum_le hx hy hz
  rw [bookTip_dist r (by decide : (0 : Fin 3) ≠ 1),
    bookTip_dist r (by decide : (1 : Fin 3) ≠ 2),
    bookTip_dist r (by decide : (2 : Fin 3) ≠ 0)] at h
  have hb := bookTip_price_le_of_triangle_le B.monotone B.submodular r B.base (B.triangle r)
  have hflat := matrix_flattening_le_asymptoticRank F hx hy hz
  have hone : 1 ≤ max (z * x) (max (x * y) (y * z)) :=
    le_trans (Nat.mul_pos hz hx) (le_max_left _ _)
  have hL := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    ((Nat.one_le_cast.mpr hone).trans hflat)
  calc
    _ = ((r 0 : ℝ) + r 1) * Real.logb 2 x + ((r 1 : ℝ) + r 2) * Real.logb 2 y +
          ((r 2 : ℝ) + r 0) * Real.logb 2 z := by
      change _ = (a 0 + a 1) * Real.logb 2 x + (a 1 + a 2) * Real.logb 2 y +
        (a 2 + a 0) * Real.logb 2 z
      simp [Fin.sum_univ_three, loads]
      ring
    _ ≤ _ := h
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hb hL

/-- The conclusion of the paper's rectangular rank theorem over a fixed field. -/
def RectangularRankBound (F : Type*) [Field F] : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z →
    let T := matrixTensor F x y z
    let m := loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z)
    RadicalTest m (Real.logb 2 (asymptoticRank T)) ∧
      RadicalTest m (Real.logb 2 (geometricBorderRank T)) ∧
      RadicalTest m (Real.logb 2 (tensorRank T))

theorem PlanarBookPrices.rectangularRankBound (B : PlanarBookPrices F) : RectangularRankBound F := by
  intro x y z hx hy hz
  dsimp only
  have h := B.heightTest hx hy hz
  have hlog (q : ℕ) (hq : 0 < q) := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    (Nat.one_le_cast.mpr hq)
  have hm := loads_nonneg (hlog x hx) (hlog y hy) (hlog z hz)
  have hl := matrix_flattening_le_asymptoticRank F hx hy hz
  have hn : 0 < max (z * x) (max (x * y) (y * z)) :=
    lt_of_lt_of_le (Nat.mul_pos hz hx) (le_max_left _ _)
  have hpos := lt_of_lt_of_le (Nat.cast_pos.mpr hn) hl
  have cmp := asymptoticRank_le_geometricBorderRank (matrixTensor F x y z)
  have hborder := h.mono (Real.logb_le_logb_of_le (by norm_num) hpos cmp)
  exact ⟨h.radicalTest hm, hborder.radicalTest hm, (hborder.mono
    (Real.logb_le_logb_of_le (by norm_num) (hpos.trans_le cmp)
      (Nat.cast_le.mpr (geometricBorderRank_le_tensorRank _)))).radicalTest hm⟩

/-- The stated square arithmetic bound follows over a field admitting the
price data. All circuit equalities in `formalOmega` are formal identities. -/
theorem PlanarBookPrices.square_exponent (B : PlanarBookPrices F) :
    3 / Real.sqrt 2 ≤ formalOmega F 1 1 1 :=
  formalOmega_square_lower_bound_of_rank_bound
    (fun x y z hx hy hz => (B.rectangularRankBound x y z hx hy hz).2.2)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
