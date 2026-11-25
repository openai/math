import OAI.Optimization.LinearProgramming.Compression.PowerBits
import OAI.Optimization.LinearProgramming.PriceGame.Model
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-! # Price queries with a real-valued hidden cost and additive tolerance

The translated and rounded costs are used only to certify the oracle transcript.
The algorithm itself only multiplies its query prices by the known rational tolerance.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace States
namespace Rounding

/-- The real-cost oracle may restrict its promise to an unknown anchored support. -/
structure Instance (N : ℕ) (anchor : Fin N) where
  positive : Bool
  active : Finset (Fin N)
  anchored : anchor ∈ active
  cost : Fin N → ℝ
  origin : ℝ
  width : ℝ
  ε : ℚ
  scale_pos : 0 < ε
  lower : ∀ i ∈ active, origin ≤ cost i
  upper : ∀ i ∈ active, cost i ≤ origin + width

variable {N : ℕ} {anchor : Fin N}

namespace Instance

variable (d : Instance N anchor)

/-- The hidden translated costs in units of the prescribed tolerance. -/
noncomputable def translated (i : Fin N) : ℝ := (d.cost i - d.origin) / (d.ε : ℝ)

/-- The range bound communicated to the integer-cost game, including zero-width inputs. -/
noncomputable def range : ℕ := max 1 ⌈d.width / (d.ε : ℝ)⌉₊

theorem translated_nonneg {i : Fin N} (hi : i ∈ d.active) : 0 ≤ d.translated i :=
  div_nonneg (sub_nonneg.mpr (d.lower i hi)) (by exact_mod_cast d.scale_pos.le)

theorem translated_le_range {i : Fin N} (hi : i ∈ d.active) : d.translated i ≤ d.range := by
  have hs : (0 : ℝ) < d.ε := by exact_mod_cast d.scale_pos
  calc
    (d.cost i - d.origin) / (d.ε : ℝ) ≤ d.width / (d.ε : ℝ) :=
      div_le_div_of_nonneg_right (by linarith [d.upper i hi]) hs.le
    _ ≤ (⌈d.width / (d.ε : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ _ := by exact_mod_cast (le_max_right 1 ⌈d.width / (d.ε : ℝ)⌉₊)

private theorem round_nonnegative {z : ℝ} (h : 0 ≤ z) : 0 ≤ round z := by
  have : (-1 : ℝ) < (round z : ℝ) := by linarith [sub_half_lt_round z]
  have : (-1 : ℤ) < round z := by exact_mod_cast this
  omega

private theorem round_toNat_le {z : ℝ} {b : ℕ} (h : z ≤ b) : (round z).toNat ≤ b := by
  have : (round z : ℝ) < (b : ℝ) + 1 := by linarith [round_le_add_half z]
  have : round z < (b : ℤ) + 1 := by exact_mod_cast this
  omega

/-- The integer game used for analysis. Inactive costs may be filled with zero. -/
noncomputable def rounded : Hidden N d.range anchor where
  positive := d.positive
  active := d.active
  anchor_mem := d.anchored
  cost i := if hi : i ∈ d.active then
    ⟨(round (d.translated i)).toNat, Nat.lt_succ_of_le (round_toNat_le (d.translated_le_range hi))⟩
    else 0

theorem error_le_half {i : Fin N} (hi : i ∈ d.active) :
    |d.translated i - ((d.rounded.cost i).val : ℝ)| ≤ 1 / 2 := by
  have h : 0 ≤ round (d.translated i) := round_nonnegative (d.translated_nonneg hi)
  have cast : ((round (d.translated i)).toNat : ℝ) = (round (d.translated i) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg h
  simpa [rounded, hi, cast] using abs_sub_round (d.translated i)

/-- The scalar sign acting on real query prices. -/
def signedPrice (z : ℝ) : ℝ := if d.positive then z else -z

/-- Real additive tolerance, with a pairwise formulation of being near the active minimum. -/
def Tolerated (q : Query N) : Prop :=
  q.index ∈ d.active ∧ ∀ j ∈ d.active,
    d.cost q.index + d.signedPrice (q.prices q.index : ℝ) ≤
      d.cost j + d.signedPrice (q.prices j : ℝ) + (d.ε : ℝ)

end Instance

/-- The computation sends only rational multiples of rational prices. -/
def scaleQuery (ε : ℚ) (q : Query N) : Query N where
  index := q.index
  prices i := ε * q.prices i

/-- An exact minimizer in the bounded integer game is an ε-minimizer for the unrounded
real costs. Each of the two rounded entries contributes at most ε/2 to the comparison. -/
theorem forced_tolerated (d : Instance N anchor) (q : Query N) (h : d.rounded.Forced q) :
    d.Tolerated (scaleQuery d.ε q) := by
  obtain ⟨hi, hm⟩ := h
  refine ⟨hi, fun j hj => ?_⟩
  have hs : (0 : ℝ) < d.ε := by exact_mod_cast d.scale_pos
  have comp : ((d.rounded.cost q.index).val : ℝ) + (d.rounded.signedPrice (q.prices q.index) : ℝ) ≤
      ((d.rounded.cost j).val : ℝ) + (d.rounded.signedPrice (q.prices j) : ℝ) := by
    exact_mod_cast hm j hj
  have ea := (abs_le.mp (d.error_le_half hi)).2
  have eb := (abs_le.mp (d.error_le_half hj)).1
  have shifted : d.translated q.index + (d.rounded.signedPrice (q.prices q.index) : ℝ) ≤
      d.translated j + (d.rounded.signedPrice (q.prices j) : ℝ) + 1 := by linarith
  have scaled := mul_le_mul_of_nonneg_left shifted hs.le
  change d.cost q.index + d.signedPrice ((d.ε * q.prices q.index : ℚ) : ℝ) ≤
    d.cost j + d.signedPrice ((d.ε * q.prices j : ℚ) : ℝ) + (d.ε : ℝ)
  have cancel (i) : (d.ε : ℝ) * d.translated i = d.cost i - d.origin := by
    exact mul_div_cancel₀ _ hs.ne'
  rw [mul_add, cancel, mul_add, mul_add, cancel, mul_one] at scaled
  cases hp : d.positive <;>
    simp [Instance.signedPrice, Hidden.signedPrice, Instance.rounded, hp] at scaled ⊢ <;> linarith

/-- Submit scaled prices without reading the real costs or their rounded values. -/
def scaleTree (ε : ℚ) : Tree N → Tree N
  | .result a => .result a
  | .ask q children => .ask (scaleQuery ε q) (fun b => scaleTree ε (children b))

theorem scaleTree_height (ε : ℚ) (t : Tree N) : (scaleTree ε t).height = t.height := by
  induction t with
  | result a => rfl
  | ask q children ih => simp [Tree.height, scaleTree, ih]

/-- For every history-dependent real-cost oracle, the scaled tree follows a permitted
transcript of the integer game with the same sequence of answers. -/
theorem reaches_scaled_run (d : Instance N anchor) (t : Tree N)
    (reply : List (Query N × Bool) → Query N → Bool)
    (valid : ∀ history q, d.Tolerated q → reply history q = d.positive)
    (history : List (Query N × Bool)) :
    Tree.Reaches d.rounded t ((scaleTree d.ε t).run reply history) := by
  induction t generalizing history with
  | result a => exact .result a
  | ask q kids ih =>
    exact .ask (fun forced => valid history _ (forced_tolerated d q forced))
      (ih (reply history (scaleQuery d.ε q)) _)

theorem scaled_run_correct (d : Instance N anchor) (t : Tree N) (correct : Tree.Correct d.rounded t)
    (reply : List (Query N × Bool) → Query N → Bool)
    (valid : ∀ history q, d.Tolerated q → reply history q = d.positive) :
    (scaleTree d.ε t).run reply [] = d.positive :=
  correct _ (reaches_scaled_run d t reply valid [])


/-- The written prices cost at most one extra copy of the rational scale's encoding
per coordinate, using the same binary register encoding as the LP machine. -/
theorem scaleQuery_priceBits (ε : ℚ) (q : Query N) :
    (∑ i, RAM.ratBits ((scaleQuery ε q).prices i)) ≤
      N * RAM.ratBits ε + ∑ i, RAM.ratBits (q.prices i) := by
  calc
    _ ≤ ∑ i, (RAM.ratBits ε + RAM.ratBits (q.prices i)) :=
      Finset.sum_le_sum fun i _ => Compression.ratBits_mul_le_add _ _
    _ = _ := by simp [Finset.sum_add_distrib]

/-- In §2 the finite costs range from zero to an integer bound, and the scale is one.
The support is the finite-cost coordinates of the winning subspace. -/
def unitInstance (side : Bool) (active : Finset (Fin N)) (ha : anchor ∈ active)
    (cost : Fin N → ℝ) (B : ℕ) (hl : ∀ i ∈ active, 0 ≤ cost i)
    (hu : ∀ i ∈ active, cost i ≤ B) : Instance N anchor where
  positive := side
  active := active
  anchored := ha
  cost := cost
  origin := 0
  width := B
  ε := 1
  scale_pos := by decide
  lower := hl
  upper := by simpa using hu

@[simp] theorem unitInstance_range (side : Bool) (active : Finset (Fin N)) (ha : anchor ∈ active)
    (cost : Fin N → ℝ) (B : ℕ) (hB : 1 ≤ B) (hl : ∀ i ∈ active, 0 ≤ cost i)
    (hu : ∀ i ∈ active, cost i ≤ B) : (unitInstance side active ha cost B hl hu).range = B := by
  simp [Instance.range, unitInstance, max_eq_right hB]

/-- An exact integer minimizer obeys the two-unit geometric label guarantee at the
unchanged prices, even when the finite costs themselves are nonintegral. -/
theorem forced_geometric (d : Instance N anchor) (he : d.ε = 1) (q : Query N)
    (h : d.rounded.Forced q) :
    q.index ∈ d.active ∧ ∀ j ∈ d.active, d.cost q.index + d.signedPrice (q.prices q.index : ℝ) ≤
      d.cost j + d.signedPrice (q.prices j : ℝ) + 2 := by
  obtain ⟨hi, hm⟩ := forced_tolerated d q h
  refine ⟨hi, fun j hj => ?_⟩
  have hh := hm j hj
  simp [scaleQuery, he] at hh
  linarith

/-- An oracle whose guarantee extends one unit past all minimizers accepts every
query required by the exact-minimum contract. -/
theorem forced_one_unit {R : ℕ} (h : Hidden N R anchor) (q : Query N) (hf : h.Forced q) :
    q.index ∈ h.active ∧ ∀ j ∈ h.active,
      (h.cost q.index : ℕ) + h.signedPrice (q.prices q.index) ≤
      (h.cost j : ℕ) + h.signedPrice (q.prices j) + 1 :=
  ⟨hf.1, fun j hj => (hf.2 j hj).trans (by linarith)⟩

end Rounding
end States
end PriceGame
end LinearProgramming
end Optimization
end OAI
