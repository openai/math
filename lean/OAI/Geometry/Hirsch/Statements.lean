import OAI.Geometry.Hirsch.Padding
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

open Filter

namespace OAI.Geometry.Hirsch

def Subpolynomial (seq : ℕ → ℕ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∀ᶠ n : ℕ in atTop, (seq n : ℝ) ≤ (n : ℝ) ^ eps

def Superpolynomial (seq : ℕ → ℕ) : Prop :=
  ∀ exponent : ℝ, ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ exponent ≤ (seq n : ℝ)

structure Example where
  poly : Polytope
  obj : poly.Objective

def MainTheorem : Prop :=
  ∀ moves : ℕ → ℕ, (∀ n, 0 < moves n) → Subpolynomial moves →
    ∃ family : ℕ → Example,
      (∀ᶠ n in atTop, let poly := (family n).poly
        Simple poly.body ∧ (graph poly.body 1).Connected ∧ poly.facetCount = n) ∧
      Subpolynomial (fun n => (family n).poly.dimension) ∧
      Superpolynomial (fun n => (family n).poly.dist (moves n)
        (family n).obj.high (family n).obj.low) ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < 1 → ∀ exponent : ℝ, ∀ᶠ n : ℕ in atTop,
        ∀ first last : (family n).poly.V, (n : ℝ) ^ (-alpha) ≤ (family n).obj.gap first last →
          (n : ℝ) ^ exponent ≤ (family n).poly.dist (moves n) first last

def ExcessTheorem : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b → ∃ c delta : ℝ, 0 < c ∧ 0 < delta ∧
    ∃ threshold : ℕ, ∀ d excess : ℕ, threshold ≤ min d excess →
      ∃ poly : Polytope, Simple poly.body ∧ (graph poly.body 1).Connected ∧
        poly.dimension = d ∧ poly.facetCount = d + excess ∧
        ∃ first last : poly.V,
          c * excess * min ((excess : ℝ) ^ a) ((d : ℝ) ^ b) ≤
            poly.dist ⌊((min d excess : ℕ) : ℝ) ^ delta⌋₊ first last

def PolynomialHirsch : Prop :=
  ∃ coeff power : ℕ, ∀ poly : Polytope, Simple poly.body → (graph poly.body 1).Connected →
    ∀ first last : poly.V, poly.dist 1 first last ≤ coeff * (poly.facetCount + 1) ^ power

def CappedSeed (degree scale mult : ℕ) (eta gamma : ℝ) : Prop :=
  ∃ poly : Polytope, ∃ obj : poly.Objective, poly.sys.Regular ∧
    (poly.dimension : ℝ) ≤ (scale : ℝ) ^ eta ∧
    (poly.facetCount : ℝ) ≤ mult * (scale : ℝ) ^ (1 + eta) ∧
    ∀ first last : poly.V,
      (obj.gap first last = 1 → mult * scale ^ degree ≤
        poly.dist ⌊(scale : ℝ) ^ gamma⌋₊ first last) ∧
      mult * (scale : ℝ) ^ (degree - 1 : ℕ) * max 0 (scale * obj.gap first last - 8) ≤
        poly.dist ⌊(scale : ℝ) ^ gamma⌋₊ first last

def CapLemma : Prop :=
  ∀ degree : ℕ, 2 ≤ degree → ∀ eta : ℝ, 0 < eta → eta < 1 →
    ∃ base : ℕ, 2 ≤ base ∧ ∃ gamma : ℝ, 0 < gamma ∧
      ∀ᶠ height : ℕ in atTop, ∀ mult : ℕ, 1 ≤ mult →
        CappedSeed degree (base ^ height) mult eta gamma

theorem not_polynomialHirsch_of_main (main : MainTheorem) : ¬ PolynomialHirsch := by
  rintro ⟨coeff, power, bound⟩
  have sub : Subpolynomial (fun _ => 1) := by
    intro eps he
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa using Real.one_le_rpow (show (1 : ℝ) ≤ n by exact_mod_cast hn) he.le
  obtain ⟨family, hf, _, hg, _⟩ := main _ (fun _ => Nat.zero_lt_one) sub
  obtain ⟨n, ⟨hs, hc, he⟩, hd, hn⟩ :=
    (hf.and ((hg (power + 1 : ℕ)).and (eventually_gt_atTop (coeff * 2 ^ power)))).exists
  rw [Real.rpow_natCast] at hd
  have lower : n ^ (power + 1) ≤ (family n).poly.dist 1 (family n).obj.high (family n).obj.low := by
    exact_mod_cast hd
  have upper := bound _ hs hc (family n).obj.high (family n).obj.low
  rw [he] at upper
  have hpos : 0 < n := by omega
  apply (lower.trans upper).not_gt
  calc
    coeff * (n + 1) ^ power ≤ coeff * (2 * n) ^ power := by gcongr; omega
    _ = (coeff * 2 ^ power) * n ^ power := by rw [mul_pow, mul_assoc]
    _ < n * n ^ power := Nat.mul_lt_mul_of_pos_right hn (pow_pos hpos _)
    _ = n ^ (power + 1) := by rw [pow_succ']

end OAI.Geometry.Hirsch
