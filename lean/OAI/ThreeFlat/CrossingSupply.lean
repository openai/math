import OAI.LinearAlgebra.SpectralBooks.ChordGraph.ChordPeeling
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace OAI
/-! # Integral supplies for the six-terminal catalytic crossing

The four numbered sites occupy vertices 0 through 3. The ends of the common
memory occupy 4 and 5. Scaling the real price comparison by `4*q` clears the
quarter widths, the phase corrections of one half, and the slack `1/(4*q)`.
-/

namespace ThreeFlat.CrossingSupply

open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators

noncomputable section

abbrev SupplyChoice := Bool × Bool × Bool

/-- One integral bundle between two of the six terminals. -/
def wire (i j : Fin 6) (h : i < j) (w : ℕ) : Widths 6 :=
  Finsupp.single (edge i j h) w

def demand (q R : ℕ) : Widths 6 :=
  wire 0 2 (by decide) (4*q) + wire 1 3 (by decide) (4*q) +
    wire 4 5 (by decide) (4*q*R)

def matching (side : Bool) (w : ℕ) : Widths 6 :=
  if side then wire 0 1 (by decide) w + wire 2 3 (by decide) w
  else wire 0 3 (by decide) w + wire 1 2 (by decide) w

def slack (w : ℕ) : Widths 6 :=
  wire 0 1 (by decide) w + wire 0 2 (by decide) w + wire 0 3 (by decide) w +
    wire 1 2 (by decide) w + wire 1 3 (by decide) w + wire 2 3 (by decide) w

def site (i : Fin 4) : Fin 6 := ⟨i.val, by omega⟩

private theorem site_lt_four (i : Fin 4) : site i < 4 := i.isLt

private theorem site_lt_five (i : Fin 4) : site i < 5 := (site_lt_four i).trans (by decide)

/-- The two terminal capacities at one numbered site. -/
def arms (i : Fin 4) (u v : ℕ) : Widths 6 :=
  wire (site i) 4 (site_lt_four i) u + wire (site i) 5 (site_lt_five i) v

/-- Opposite shifts at a pair of sites leave each end's total capacity fixed. -/
def transfer (q R : ℕ) (i j : Fin 4) (sign : Bool) : Widths 6 :=
  let high := (R+2)*q
  let low := (R-2)*q
  if sign then arms i high low + arms j low high
  else arms i low high + arms j high low

def supply (q R : ℕ) (c : SupplyChoice) : Widths 6 :=
  matching c.1 (4*q) + slack 2 +
    (transfer q R 0 2 c.2.1 + transfer q R 1 3 c.2.2)

/-- Sum of wire lengths, weighted by integer multiplicity. -/
def cost (d : Fin 6 → Fin 6 → ℝ) : Widths 6 →+ ℝ where
  toFun g := ∑ e : Chord 6, (g e : ℝ) * d e.1.1 e.1.2
  map_zero' := by simp
  map_add' := by
    intro g h
    simp [add_mul, Finset.sum_add_distrib]

@[simp] theorem cost_wire (d : Fin 6 → Fin 6 → ℝ) (i j : Fin 6) (h : i < j) (w : ℕ) :
    cost d (wire i j h w) = w * d i j := by
  classical
  change (∑ e : Chord 6, ((Finsupp.single (edge i j h) w) e : ℝ) * d e.1.1 e.1.2) = _
  rw [Finset.sum_eq_single (edge i j h)]
  · simp [edge]
  · intro e _ he
    simp [he]
  · simp

@[simp] theorem load_wire (v i j : Fin 6) (h : i < j) (w : ℕ) :
    load v (wire i j h w) = ((if v = i then 1 else 0) + (if v = j then 1 else 0)) * w :=
  load_single _ _ _

theorem supply_load_four (q R : ℕ) (hR : 2 ≤ R) (c : SupplyChoice) :
    load 4 (supply q R c) = 4*q*R := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hR
  obtain ⟨a,b,c⟩ := c
  cases a <;> cases b <;> cases c <;>
    norm_num [supply, matching, slack, transfer, arms, site] <;> ring

theorem supply_load_five (q R : ℕ) (hR : 2 ≤ R) (c : SupplyChoice) :
    load 5 (supply q R c) = 4*q*R := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hR
  obtain ⟨a,b,c⟩ := c
  cases a <;> cases b <;> cases c <;>
    norm_num [supply, matching, slack, transfer, arms, site] <;> ring

def beta (d : Fin 6 → Fin 6 → ℝ) (i : Fin 4) : ℝ := d (site i) 4 - d (site i) 5

private theorem maximizing_transfer (d : Fin 6 → Fin 6 → ℝ) (q R : ℕ) (hR : 2 ≤ R)
    (i j : Fin 4) :
    ∃ sign, cost d (transfer q R i j sign) =
      (R : ℝ)*q*(d (site i) 4 + d (site i) 5 + d (site j) 4 + d (site j) 5) +
        2*q*|beta d i - beta d j| := by
  by_cases h : 0 ≤ beta d i - beta d j
  · refine ⟨true, ?_⟩
    rw [abs_of_nonneg h]
    simp [transfer, arms, beta, Nat.cast_sub hR]
    ring
  · refine ⟨false, ?_⟩
    rw [abs_of_neg (lt_of_not_ge h)]
    simp [transfer, arms, beta, Nat.cast_sub hR]
    ring

private theorem maximizing_side (d : Fin 6 → Fin 6 → ℝ) (q : ℕ) :
    ∃ b, cost d (matching b (4*q)) = (4*q:ℝ)*max (d 0 1+d 2 3) (d 0 3+d 1 2) := by
  rcases le_total (d 0 1+d 2 3) (d 0 3+d 1 2) with h | h
  · exact ⟨false, by rw [max_eq_right h]; simp [matching]; ring⟩
  · exact ⟨true, by rw [max_eq_left h]; simp [matching]; ring⟩

/-- The corrected tree inequality covers the priced demand by one of eight
integral supplies. In particular no spectral-point-dependent selector is
required once the fixed list of supplies is given to strict comparison. -/
theorem exists_cost_cover (d : Fin 6 → Fin 6 → ℝ)
    (hsym : ∀ i j, d i j = d j i) (hdiag : ∀ i, d i i = 0)
    (q R : ℕ) (hq : 0 < q) (hR : 2 ≤ R)
    (crossPrice :
      d 0 2 + d 1 3 ≤ max (d 0 1 + d 2 3) (d 0 3 + d 1 2) +
        1 / (4*(q:ℝ)) * (∑ i : Fin 4, ∑ j : Fin 4, d (site i) (site j)) +
        (|beta d 0 - beta d 2| + |beta d 1 - beta d 3|)/2 +
        ((R:ℝ)/4) * ∑ i : Fin 4, (d (site i) 4 + d (site i) 5 - d 4 5)) :
    ∃ c : SupplyChoice, cost d (demand q R) ≤ cost d (supply q R c) := by
  obtain ⟨s,hs⟩ := maximizing_side d q
  obtain ⟨u,hu⟩ := maximizing_transfer d q R hR 0 2
  obtain ⟨v,hv⟩ := maximizing_transfer d q R hR 1 3
  refine ⟨⟨s,u,v⟩, ?_⟩
  simp only [supply, map_add, hs, hu, hv, demand, slack, cost_wire, Nat.cast_mul, Nat.cast_ofNat]
  have mass :
      (∑ i : Fin 4, ∑ j : Fin 4, d (site i) (site j)) =
      2 * (d 0 1 + d 0 2 + d 0 3 + d 1 2 + d 1 3 + d 2 3) := by
    simp [Fin.sum_univ_four, site, hdiag]
    linarith [hsym 1 0, hsym 2 0, hsym 3 0, hsym 2 1, hsym 3 1, hsym 3 2]
  rw [mass] at crossPrice
  simp only [Fin.sum_univ_four] at crossPrice
  have scaled := mul_le_mul_of_nonneg_left crossPrice (show 0 ≤ 4*(q:ℝ) by positivity)
  have cancel (a : ℝ) : (4*(q:ℝ))*(1/(4*(q:ℝ))*a) = a := by
    field_simp [show (q:ℝ) ≠ 0 by positivity]
  conv at scaled => rhs; rw [mul_add, mul_add, mul_add, cancel]
  norm_num [site] at scaled ⊢
  linarith only [scaled]

end
end ThreeFlat.CrossingSupply

end OAI
