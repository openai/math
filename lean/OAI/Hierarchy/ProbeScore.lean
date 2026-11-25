import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

namespace OAI
/-! # The signed-altimeter score and the saving on a purchased probe -/

namespace Hierarchy.AdaptiveProbe

open scoped BigOperators
noncomputable section

def rise (M x : ℝ) : ℝ := max (x - M) 0

def rowScore (a b M x : ℝ) := a * x^2 + b * (rise M x)^2

def rowSlope (a b M x : ℝ) := 2*a*x + 2*b*rise M x

def rowDivergence (a b M x y : ℝ) :=
  rowScore a b M y - rowScore a b M x - rowSlope a b M x * (y-x)

theorem rise_nonneg (M x : ℝ) : 0 ≤ rise M x := le_max_right _ _

theorem rise_divergence (M x y : ℝ) :
    (rise M y - rise M x)^2 ≤
      (rise M y)^2 - (rise M x)^2 - 2 * rise M x * (y-x) := by
  by_cases h : x ≤ M
  · rw [show rise M x = 0 from max_eq_right (sub_nonpos.mpr h)]
    ring_nf
    exact le_rfl
  · rw [show rise M x = x - M from max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
    have hy : y - M ≤ rise M y := le_max_left _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge h)) (sub_nonneg.mpr hy)]

theorem rowDivergence_lower (a b M x y : ℝ) (hb : 0 ≤ b) :
    a*(y-x)^2 + b*(rise M y - rise M x)^2 ≤ rowDivergence a b M x y := by
  unfold rowDivergence rowScore rowSlope
  nlinarith only [mul_le_mul_of_nonneg_left (rise_divergence M x y) hb]

variable {I : Type*} [Fintype I]

/-- The normalization by the population size is included in the two coefficients.
The second coefficient vanishes on the ordinary payload commodities. -/
def score (a M : ℝ) (b x : I → ℝ) : ℝ := ∑ i, rowScore a (b i) M (x i)

def pairing (v x : I → ℝ) : ℝ := ∑ i, v i * x i

def divergence (a M : ℝ) (b x y : I → ℝ) : ℝ :=
  score a M b y - score a M b x -
    pairing (fun i => rowSlope a (b i) M (x i)) (fun i => y i-x i)

theorem divergence_eq_sum (a M : ℝ) (b x y : I → ℝ) :
    divergence a M b x y = ∑ i, rowDivergence a (b i) M (x i) (y i) := by
  simp only [divergence, score, pairing, rowDivergence, Finset.sum_sub_distrib]

theorem divergence_lower (a M : ℝ) (b x y : I → ℝ) (hb : ∀ i, 0 ≤ b i) :
    (∑ i, (a*(y i-x i)^2 + b i*(rise M (y i)-rise M (x i))^2)) ≤
      divergence a M b x y := by
  rw [divergence_eq_sum]
  exact Finset.sum_le_sum fun i _ => rowDivergence_lower _ _ _ _ _ (hb i)

/-- The common signed coordinate on the chain telescopes. The estimates on
the post-purchase readings and the cap on the probe force a halved reading. -/
theorem chain_drop (H : ℕ) {δ η : ℝ} (pos : η < δ)
    (long : 1 + η < (H : ℝ)*(δ-η)) (z : ℕ → ℝ) (v v' : Fin H → ℝ)
    (marked : ∀ i, 2*δ ≤ v i)
    (measured : ∀ i, |v' i-max (z (i.val+1)-z i.val) 0| ≤ η)
    (probe : z H - z 0 ≤ 1+η) : ∃ i, v' i ≤ v i/2 := by
  by_contra! no
  have step (i : Fin H) : δ-η ≤ z (i.val+1)-z i.val := by
    have hi := (abs_le.mp (measured i)).2
    have larger : δ-η < max (z (i.val+1)-z i.val) 0 := by linarith [no i, marked i]
    exact le_of_lt ((lt_max_iff.mp larger).resolve_right (by linarith))
  have add (m : ℕ) (hm : m ≤ H) : (m : ℝ)*(δ-η) ≤ z m - z 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
      have lo := ih (by omega)
      have hi := step ⟨m, by omega⟩
      change δ-η ≤ z (m+1) - z m at hi
      rw [Nat.cast_succ]
      linarith
  linarith [add H le_rfl]

/-- One distinct halved coordinate pays the divergence fee of each accurate
chain. This leaves every unselected coordinate free to change. -/
theorem purchased_divergence (a M s β u : ℝ) (b x y : I → ℝ)
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hβ : 0 ≤ β) (hb : ∀ i, 0 ≤ b i)
    (changed : Finset I) (weight : ∀ i ∈ changed, β ≤ b i)
    (marked : ∀ i ∈ changed, u ≤ s*(rise M (x i))^2)
    (halved : ∀ i ∈ changed, rise M (y i) ≤ rise M (x i)/2) :
    (changed.card : ℝ) * (β*u/8) ≤ (s/2) * divergence a M b x y := by
  let R (i : I) := rowDivergence a (b i) M (x i) (y i)
  have nonneg (i : I) : 0 ≤ R i :=
    (add_nonneg (mul_nonneg ha (sq_nonneg _)) (mul_nonneg (hb i) (sq_nonneg _))).trans
      (rowDivergence_lower _ _ _ _ _ (hb i))
  have gain (i : I) (hi : i ∈ changed) : β*u/8 ≤ (s/2)*R i := by
    let t := rise M (x i)
    let r := rise M (y i)
    have shrink : t/2 ≤ t-r := by have := halved i hi; dsimp [t,r]; linarith
    have ht : 0 ≤ t := rise_nonneg _ _
    have sq : t^2/4 ≤ (r-t)^2 := by
      nlinarith [sq_le_sq' (a:=t/2) (b:=t-r) (by linarith) shrink]
    have product : β*(t^2/4) ≤ b i*(r-t)^2 :=
      mul_le_mul (weight i hi) sq (by positivity) (hb i)
    have term : β*(t^2/4) ≤ R i :=
      product.trans ((le_add_of_nonneg_left (mul_nonneg ha (sq_nonneg _))).trans
        (rowDivergence_lower _ _ _ _ _ (hb i)))
    have stock := mul_le_mul_of_nonneg_left (marked i hi) hβ
    change β*u ≤ β*(s*t^2) at stock
    nlinarith only [stock, mul_le_mul_of_nonneg_left term (show 0 ≤ s/2 by positivity)]
  calc
    _ = ∑ _i ∈ changed, β*u/8 := by simp
    _ ≤ ∑ i ∈ changed, (s/2)*R i := Finset.sum_le_sum gain
    _ ≤ ∑ i, (s/2)*R i := Finset.sum_le_univ_sum_of_nonneg (fun i => mul_nonneg (by positivity) (nonneg i))
    _ = _ := by rw [divergence_eq_sum, Finset.mul_sum]

end
end Hierarchy.AdaptiveProbe

end OAI
