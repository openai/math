import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Iteration of the length and concentration estimates

In Lemma 6.1 every pack in round `j` represents `K^j` original packs. Equation (6.3)
averages the lengths of its children but uses the maximum of their concentrations.
The two coordinates therefore have to be bounded separately before combining them
in the final site cost.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Filter Topology
open scoped BigOperators

/-- The packs and charged quantities in a sequence of combining rounds. -/
structure Batch (K : ℕ) where
  /-- Packs in a round, including any alternative summands that occur there. -/
  Packs : ℕ → Type*
  /-- The `K` input packs combined at a node. -/
  child : ∀ {j}, Packs (j + 1) → Fin K → Packs j
  /-- Total charged length with bit multiplicity. -/
  length : ∀ {j}, Packs j → ℝ
  /-- Tile concentration of positive-length bits. -/
  concentration : ∀ {j}, Packs j → ℝ

/-- Equation (6.3) through round `b`, with `V` a common upper bound on the tile counts. -/
def Batch.Estimates {K : ℕ} (T : Batch K) (hK : 0 < K) (b : ℕ) (r C V : ℝ) : Prop :=
  ∀ j < b, ∀ p : T.Packs (j + 1),
    let average := (∑ i, T.length (T.child p i)) / K
    let maximum := Finset.univ.sup' ⟨⟨0, hK⟩, Finset.mem_univ _⟩
      (fun i => T.concentration (T.child p i))
    T.length p / K ≤ r * average + C * (Real.sqrt K)⁻¹ * maximum + C * V ∧
    T.concentration p / K ≤ C * (average + (Real.sqrt K)⁻¹ * maximum)

/-- Componentwise majorant for per-original-input length and concentration. -/
def envelope (r C t V w x : ℝ) : ℕ → ℝ × ℝ
  | 0 => (w, x)
  | n + 1 =>
    let y := envelope r C t V w x n
    (r * y.1 + C * t * y.2 + C * V, C * (y.1 + t * y.2))

/-- Applying (6.3) to arbitrary children preserves both envelope bounds, with the
unnormalized totals at round `j` multiplied by exactly `K^j`. -/
theorem Batch.le_envelope {K b : ℕ} (T : Batch K) {hK : 0 < K} {r C V w x : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hV : 0 ≤ V) (hstep : T.Estimates hK b r C V)
    (hinput : ∀ p : T.Packs 0, T.length p ≤ w ∧ T.concentration p ≤ x) :
    ∀ j ≤ b, ∀ p : T.Packs j,
      let y := envelope r C (Real.sqrt K)⁻¹ V w x j
      T.length p ≤ (K : ℝ)^j * y.1 ∧ T.concentration p ≤ (K : ℝ)^j * y.2 := by
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hk1 : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have ht : 0 ≤ (Real.sqrt K)⁻¹ := by positivity
  intro j
  induction j with
  | zero => simpa [envelope] using fun (_ : 0 ≤ b) => hinput
  | succ j ih =>
    intro hj p
    let y := envelope r C (Real.sqrt K)⁻¹ V w x j
    let S := (K : ℝ)^j
    have inputs (i : Fin K) := ih (by omega) (T.child p i)
    have havg : (∑ i, T.length (T.child p i)) / K ≤ S * y.1 := by
      apply (div_le_iff₀ hk).2
      calc
        _ ≤ ∑ _ : Fin K, S * y.1 := Finset.sum_le_sum fun i _ => (inputs i).1
        _ = _ := by simp [mul_comm]
    have hmax : Finset.univ.sup' ⟨⟨0, hK⟩, Finset.mem_univ _⟩
        (fun i => T.concentration (T.child p i)) ≤ S * y.2 :=
      Finset.sup'_le _ _ fun i _ => (inputs i).2
    have hround : C * V ≤ S * (C * V) := le_mul_of_one_le_left (mul_nonneg hC hV)
      (one_le_pow₀ hk1)
    obtain ⟨hw, hx⟩ := hstep j (by omega) p
    have hlen := hw.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left havg hr)
      (mul_le_mul_of_nonneg_left hmax (mul_nonneg hC ht))) hround)
    have hconc := hx.trans (mul_le_mul_of_nonneg_left
      (add_le_add havg (mul_le_mul_of_nonneg_left hmax ht)) hC)
    constructor
    · calc
        _ ≤ _ := (div_le_iff₀ hk).mp hlen
        _ = _ := by change _ = (K : ℝ)^(j+1) * (r * y.1 + C * (Real.sqrt K)⁻¹ * y.2 + C * V)
                    dsimp [S]; ring
    · calc
        _ ≤ _ := (div_le_iff₀ hk).mp hconc
        _ = _ := by change _ = (K : ℝ)^(j+1) * (C * (y.1 + (Real.sqrt K)⁻¹ * y.2))
                    dsimp [S]; ring

private theorem envelope_linear (r C t V M w x : ℝ) (n : ℕ) :
    envelope r C t V (M * w) (M * x) n =
      (M * (envelope r C t 0 w x n).1 + V * (envelope r C t 1 0 0 n).1,
       M * (envelope r C t 0 w x n).2 + V * (envelope r C t 1 0 0 n).2) := by
  induction n with
  | zero => simp [envelope]
  | succ n ih => simp only [envelope, ih, Prod.mk.injEq]; constructor <;> ring

private theorem continuous_envelope (r C V w x : ℝ) (n : ℕ) :
    Continuous (fun t => envelope r C t V w x n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hf := ih.fst
    have hs := ih.snd
    change Continuous (fun t => (_, _))
    exact ((continuous_const.mul hf).add ((continuous_const.mul continuous_id).mul hs)
      |>.add continuous_const).prodMk (continuous_const.mul (hf.add (continuous_id.mul hs)))

private theorem envelope_zero_fst (r C w x : ℝ) (n : ℕ) :
    (envelope r C 0 0 w x n).1 = r^n * w := by
  induction n with
  | zero => simp [envelope]
  | succ n ih => simp [envelope, ih, pow_succ', mul_assoc]

private theorem envelope_zero_snd (r C w x : ℝ) (n : ℕ) :
    (envelope r C 0 0 w x (n+1)).2 = C * (r^n * w) := by
  simp [envelope, envelope_zero_fst]

/-- The normalized output site cost has coefficient at most `1/2` on the maximum
input cost. The number of steps is chosen before the pattern constants `C`,
`Cin` and `Cout`; the site weight is chosen before the sufficiently large
integer fan-in. Here `A` bounds nonlocal rounded bits by charged length and `L`
bounds initial length by nonlocal bits. -/
theorem exists_shortening_epoch {r L A : ℝ} (hr : 0 ≤ r) (hr' : r < 1)
    (hL : 0 ≤ L) (hA : 0 ≤ A) :
    ∃ b : ℕ, 0 < b ∧ ∀ C Cin Cout : ℝ, 0 ≤ C → 0 ≤ Cin → 0 ≤ Cout →
      ∃ weight : ℝ, 0 < weight ∧ ∃ E : ℝ, 0 < E ∧
        ∀ᶠ K : ℕ in atTop, ∃ hK : 0 < K, ∀ (T : Batch K) (M V : ℝ), 0 ≤ M → 0 ≤ V →
          T.Estimates hK b r C V →
          (∀ p : T.Packs 0, T.length p ≤ M * L ∧ T.concentration p ≤ M * (Cin / weight)) →
          ∀ p : T.Packs b,
            (A * T.length p + weight * Cout * T.concentration p) / (K : ℝ)^b ≤
              M / 2 + E * V := by
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr').const_mul (A * L)
  have hsmall : ∀ᶠ b : ℕ in atTop, A * L * r^b < 1/8 :=
    (by simpa using hlim : Tendsto (fun b : ℕ => A * L * r^b) atTop (𝓝 0)).eventually
      (gt_mem_nhds (by norm_num))
  obtain ⟨b, hb⟩ := eventually_atTop.mp hsmall
  refine ⟨b+1, by omega, ?_⟩
  intro C Cin Cout hC _ hCout
  let D := Cout * (C * (r^b * L))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let weight := 1 / (8 * (D + 1))
  have hweight : 0 < weight := by dsimp [weight]; positivity
  have hweighted : weight * D < 1/8 := by
    dsimp [weight]; rw [one_div_mul_eq_div, div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  let cost := fun t V w x : ℝ =>
    A * (envelope r C t V w x (b+1)).1 + weight * Cout * (envelope r C t V w x (b+1)).2
  have cont (V w x : ℝ) : Continuous (fun t => cost t V w x) :=
    (continuous_const.mul (continuous_envelope _ _ _ _ _ _).fst).add
      (continuous_const.mul (continuous_envelope _ _ _ _ _ _).snd)
  have hcost : cost 0 0 L (Cin / weight) < 1/2 := by
    dsimp only [cost]
    rw [envelope_zero_fst, envelope_zero_snd]
    dsimp only [D] at hweighted
    linarith only [hb (b+1) (by omega), hweighted]
  let E := max 0 (cost 0 1 0 0) + 1
  have hE : 0 < E := by dsimp [E]; linarith [le_max_left 0 (cost 0 1 0 0)]
  have htiles : cost 0 1 0 0 < E := by dsimp [E]; linarith [le_max_right 0 (cost 0 1 0 0)]
  have ht : Tendsto (fun K : ℕ => (Real.sqrt K)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have eventual (V w x e : ℝ) (he : cost 0 V w x < e) :
      ∀ᶠ K : ℕ in atTop, cost (Real.sqrt K)⁻¹ V w x < e :=
    ((cont V w x).continuousAt.tendsto.comp ht).eventually (gt_mem_nhds he)
  refine ⟨weight, hweight, E, hE, ?_⟩
  filter_upwards [eventual 0 L (Cin / weight) _ hcost, eventual 1 0 0 E htiles,
    eventually_gt_atTop 0] with K hinputCoeff htileCoeff hK
  refine ⟨hK, ?_⟩
  intro T M V hM hV hstep hinput p
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  obtain ⟨hw, hx⟩ := T.le_envelope hr hC hV hstep hinput _ le_rfl p
  have hbound := add_le_add (mul_le_mul_of_nonneg_left hw hA)
    (mul_le_mul_of_nonneg_left hx (mul_nonneg hweight.le hCout))
  apply (div_le_iff₀ (pow_pos hk _)).mpr
  apply hbound.trans
  rw [envelope_linear]
  calc
    _ = (M * cost (Real.sqrt K)⁻¹ 0 L (Cin / weight) + V * cost (Real.sqrt K)⁻¹ 1 0 0) *
        (K : ℝ)^(b+1) := by dsimp only [cost]; ring
    _ ≤ (M * (1/2) + V * E) * (K : ℝ)^(b+1) :=
      mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left hinputCoeff.le hM)
        (mul_le_mul_of_nonneg_left htileCoeff.le hV)) (pow_nonneg hk.le _)
    _ = _ := by ring

end Shortening

end BorderVNP
end Computability
end OAI
