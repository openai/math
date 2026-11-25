import OAI.LinearAlgebra.MatrixExponent.FieldFormula
import OAI.LinearAlgebra.MatrixExponent.Rectangle

/-! # Dual exponents and finite rank bounds over every field -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Consequences
open Filter Set

section

variable (F : Type*) [Field F]

theorem dual_formula {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    dual F a b = a * b / (a + b) ∧
    IsGreatest {c ∈ Icc 0 (min a b) | exponent F a b c = a + b} (a * b / (a + b)) := by
  have h := greatest (omega_eq_and_rigidity F).2 (omega_eq F) ha hb
  exact ⟨h.csSup_eq, h⟩

theorem square_output {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1) :
    dual F 1 1 = 1 / 2 ∧
      exponent F 1 1 c = if c ≤ 1 / 2 then 2 else 2 + (c - 1 / 2) ^ 2 / c := by
  obtain ⟨hs, hr⟩ := omega_eq_and_rigidity F
  exact ⟨dual_square hr hs, Rectangle.square_output hr hs hc hc'⟩

theorem minimum {i j k : ℕ} (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    asymptoticRank (ordinary F i j k) = Real.exp (U (Real.log i) (Real.log j) (Real.log k)) ∧
    IsLeast {s | ∃ w : Fin i → Fin j → Fin k → F,
      (∀ a b c, w a b c ≠ 0) ∧ asymptoticRank w = s}
      (Real.exp (U (Real.log i) (Real.log j) (Real.log k))) := by
  exact minimum_eq_benchmark (omega_eq_and_rigidity F).2 (omega_eq F) hi hj hk

theorem square_rank {s : ℕ} (hs : 0 < s) :
    asymptoticRank (ordinary F s s s) = (s : ℝ) ^ (9 / 4 : ℝ) := by
  rw [ordinary_square F hs, omega_eq]

theorem preservation {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (w : ∀ n, Fin (side n a) → Fin (side n b) → Fin (side n c) → F)
    (hd : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-ε) ≤ density (w n)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (U a b c - ε) ≤ asymptoticRank (w n) ∧
      ∀ r, BorderRankLE (w n) r → (n : ℝ) ^ (U a b c - ε) ≤ r := by
  rw [← exponent_eq F ha hb hc]
  exact Sparse.preservation F ha hb hc w hd hε

end

section

variable {F : Type*} [Field F] {i j k r : ℕ} {w : Fin i → Fin j → Fin k → F}

private theorem log_formula (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    exponent F (Real.log i) (Real.log j) (Real.log k) = U (Real.log i) (Real.log j) (Real.log k) :=
  exponent_eq F (Real.log_nonneg (by exact_mod_cast hi)) (Real.log_nonneg (by exact_mod_cast hj))
    (Real.log_nonneg (by exact_mod_cast hk))

theorem density_lower (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) (hw : 0 < density w) :
    density w * Real.exp (U (Real.log i) (Real.log j) (Real.log k)) ≤ asymptoticRank w := by
  rw [← log_formula (F := F) hi hj hk]
  exact asymptotic_density hi hj hk hw

theorem support_lower (hw : (Sparse.support w).Nonempty) :
    (supportSize w : ℝ) ^ (3 / 4 : ℝ) * (2 : ℝ) ^ (Sparse.premium (Sparse.support w) / 4) ≤ asymptoticRank w := by
  exact Sparse.support_exponent w (omega_eq F) hw

theorem grouped (h : BorderRankLE w r) (hw : ∀ a b c, w a b c ≠ 0)
    (hvol : 1 < i * j * k) {g : ℕ} (hg : 2 * largest i j k < g) :
    let d := largest i j k
    let ρ := Real.exp (U (Real.log i) (Real.log j) (Real.log k))
    let a := Real.log ρ / Real.log ((i : ℝ) * j * k)
    ρ + (⌊ρ / g⌋₊ : ℝ) * (((g : ℝ) - d) ^ a - (d : ℝ) ^ a) ≤ r ∧ ((d : ℝ) < ρ → ρ < (r : ℝ)) := by
  have hi : 0 < i := Nat.pos_of_ne_zero (by rintro rfl; simp at hvol)
  have hj : 0 < j := Nat.pos_of_ne_zero (by rintro rfl; simp at hvol)
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hvol)
  rw [← log_formula (F := F) hi hj hk]
  exact ⟨h.grouped hw hvol hg, h.strict hw hvol⟩

attribute [local instance 10000] ContinuousMul.to_continuousSMul

theorem directional (h : BorderRankLE w r) (hw : ∀ a b c, w a b c ≠ 0)
    (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) {g : ℕ} (hg : 2 * largest i j k < g) (e : Fin 3) :
    let d := largest i j k
    let ρ := Real.exp (U (Real.log i) (Real.log j) (Real.log k))
    let θ := partialRight U (Real.log i) (Real.log j) (Real.log k) e
    HasDerivWithinAt (vary U (Real.log i) (Real.log j) (Real.log k) e) θ (Ici 0) 0 ∧
      ρ + (⌊ρ / g⌋₊ : ℝ) * (((g : ℝ) - d) ^ θ - (d : ℝ) ^ θ) ≤ r := by
  exact h.directional_benchmark hw (omega_eq_and_rigidity F).2 (omega_eq F) hi hj hk hg e

end

open Sums in
theorem heterogeneous (F : Type) [Field F] {n : ℕ} (v : Fin n → Shape) (hn : 0 < n) :
    IsLeast {s | ∃ w : ∀ t, Weights F (v t), (∀ t a b c, w t a b c ≠ 0) ∧
      asymptotic (blocks v w) = s} (asymptotic (blocks v (unweighted F v))) ∧
    IsGreatest (objective U v '' Sums.simplex n)
      (Real.log (asymptotic (blocks v (unweighted F v)))) := by
  exact ⟨(Sums.minimum F v hn).1, benchmark_maximum v hn (omega_eq_and_rigidity F).2 (omega_eq F)⟩

theorem square_border_surplus {K : ℕ → Type*} [∀ n, Field (K n)]
    (w : ∀ n, Fin n → Fin n → Fin n → K n) (hw : ∀ n a b c, w n a b c ≠ 0)
    (r : ℕ → ℕ) (hr : ∀ n, BorderRankLE (w n) (r n)) {c : ℝ} (hc : c < Speedup.cStar) :
    ∀ᶠ s : ℕ in atTop, (s : ℝ) ^ (9 / 4 : ℝ) + c * (s : ℝ) ^ (7 / 4 : ℝ) ≤ r s := by
  exact Rectangle.square_border_surplus (fun n => omega_eq (K n)) w hw r hr hc

theorem exact_surplus {K : ℕ → Type*} [∀ n, Field (K n)] {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1)
    (w : ∀ n, Fin (side n x) → Fin (side n y) → Fin (side n (x * y)) → K n)
    (hw : ∀ n a b c, w n a b c ≠ 0) (r : ℕ → ℕ) (hr : ∀ n, WeightedRankLE (w n) (r n))
    {L : ℝ} (hL : L < Real.exp (-2) * max ((x / y) ^ 2) ((y / x) ^ 2)) :
    ∀ᶠ n in atTop, L < normalized x y r n := by
  exact Rectangle.exact_surplus hx hy hxy (fun n => (omega_eq_and_rigidity (K n)).2)
    (fun n => omega_eq (K n)) w hw r hr hL

theorem border_surplus {K : ℕ → Type*} [∀ n, Field (K n)] {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1)
    (w : ∀ n, Fin (side n x) → Fin (side n y) → Fin (side n (x * y)) → K n)
    (hw : ∀ n a b c, w n a b c ≠ 0) (r : ℕ → ℕ) (hr : ∀ n, BorderRankLE (w n) (r n))
    {L : ℝ} (hL : L < Real.exp (-2) * min ((x / y) ^ 2) ((y / x) ^ 2)) :
    ∀ᶠ n in atTop, L < normalized x y r n := by
  exact Rectangle.border_surplus hx hy hxy (fun n => (omega_eq_and_rigidity (K n)).2)
    (fun n => omega_eq (K n)) w hw r hr hL

theorem scaled_exact_surplus {K : ℕ → Type*} [∀ n, Field (K n)] {x y a : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) (ha : 0 < a)
    (w : ∀ n, Fin (side n x) → Fin (side n y) → Fin (Threshold.width n x y a) → K n)
    (hw : ∀ n a b c, w n a b c ≠ 0) (r : ℕ → ℕ) (hr : ∀ n, WeightedRankLE (w n) (r n))
    {L : ℝ} (hL : L < Threshold.optimum (Real.log a / (x * y)) (max (x / y) (y / x))) :
    ∀ᶠ n in atTop, L < normalized x y r n := by
  exact Rectangle.scaled_exact_surplus hx hy hxy ha (fun n => (omega_eq_and_rigidity (K n)).2)
    (fun n => omega_eq (K n)) w hw r hr hL

theorem scaled_border_surplus {K : ℕ → Type*} [∀ n, Field (K n)] {x y a : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) (ha : 0 < a)
    (w : ∀ n, Fin (side n x) → Fin (side n y) → Fin (Threshold.width n x y a) → K n)
    (hw : ∀ n a b c, w n a b c ≠ 0) (r : ℕ → ℕ) (hr : ∀ n, BorderRankLE (w n) (r n))
    {L : ℝ} (hL : L < Threshold.optimum (Real.log a / (x * y)) (min (x / y) (y / x))) :
    ∀ᶠ n in atTop, L < normalized x y r n := by
  exact Rectangle.scaled_border_surplus hx hy hxy ha (fun n => (omega_eq_and_rigidity (K n)).2)
    (fun n => omega_eq (K n)) w hw r hr hL

theorem square_threshold {K : ℕ → Type*} [∀ n, Field (K n)] {a : ℝ}
    (ha : 0 < a) (ha' : a ≤ Real.sqrt (Real.exp 1))
    (w : ∀ s, Fin s → Fin s → Fin ⌈a * Real.sqrt s⌉₊ → K s)
    (hw : ∀ s i j k, w s i j k ≠ 0) (r : ℕ → ℕ) (hr : ∀ s, BorderRankLE (w s) (r s))
    {L : ℝ} (hL : L < Real.exp (-2) * a ^ 4) :
    ∀ᶠ s : ℕ in atTop, L < ((r s : ℝ) - (s : ℝ) ^ 2) * Real.log ((s : ℝ) ^ 2) / (s : ℝ) ^ 2 := by
  exact Rectangle.square_threshold ha ha' (fun n => (omega_eq_and_rigidity (K n)).2)
    (fun n => omega_eq (K n)) w hw r hr hL

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Consequences
