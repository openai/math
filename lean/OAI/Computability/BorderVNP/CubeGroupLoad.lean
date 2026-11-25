import OAI.Computability.BorderVNP.CubePackets
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Padding and group incidence in the cube schedule

Every ordered pair of labels receives the same width, an integer multiple of the
packet block width. A group selected by one coordinate contains exactly a (1/d)
fraction of the labels. Every raw wire in a packet meeting the group has one end
in that group, giving the factor two in the raw-load estimate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube

open Finset

/-- Padded width per ordered pair in Section 8.2. -/
noncomputable def pairWidth (W : ℝ) (b Z : ℕ) : ℕ :=
  b * ⌈4*W/(b*Z^2 : ℕ)⌉₊

/-- Padding uses less than one extra block per label pair. -/
theorem pairWidth_bounds {W : ℝ} (hW : 0 ≤ W) {b Z : ℕ} (hb : 0 < b) (hZ : 0 < Z) :
    4*W ≤ (pairWidth W b Z : ℝ)*Z^2 ∧
      (pairWidth W b Z : ℝ)*Z^2 < 4*W + b*Z^2 := by
  let D := (b * Z^2 : ℕ)
  have hD : (0 : ℝ) < D := by dsimp [D]; positivity
  have lo := (div_le_iff₀ hD).mp (Nat.le_ceil (4*W/D))
  have hi := Nat.ceil_lt_add_one (show 0 ≤ 4*W/D by positivity)
  have hi' := (mul_lt_mul_iff_left₀ hD).mpr hi
  rw [add_mul,div_mul_cancel₀ _ hD.ne',one_mul] at hi'
  simp only [pairWidth,Nat.cast_mul]
  dsimp [D] at lo hi'
  push_cast at lo hi' ⊢
  constructor <;> linarith only [lo,hi']

/-- A group with symbol `s` at coordinate `i` counts exactly the padded wires
having at least one endpoint in that group. -/
def groupRaw {n d : ℕ} (S : ℕ) (i : Fin (n+1)) (s : Fin d) :=
  ∑ u : Label (n+1) d, ∑ v : Label (n+1) d, if u i = s ∨ v i = s then S else 0

/-- Fixing one coordinate leaves exactly one free choice at each of the other coordinates. -/
theorem card_fixed_symbol {n d : ℕ} (i : Fin (n+1)) (s : Fin d) :
    (Finset.univ.filter fun u : Label (n+1) d ↦ u i = s).card = d^n := by
  simpa only [Fintype.piFinset_univ, Finset.card_univ, Fintype.card_fin,
      Nat.add_sub_cancel] using Fintype.card_filter_piFinset_const_eq_of_mem
        (Finset.univ : Finset (Fin d)) i (Finset.mem_univ s)

/-- Raw load is at most `2P/d` with `P = S*(d^(n+1))²`. -/
theorem groupRaw_le {n d : ℕ} (S : ℕ) (i : Fin (n+1)) (s : Fin d) :
    groupRaw S i s * d ≤ 2*(S*(d^(n+1))^2) := by
  let wt (u : Label (n+1) d) := if u i = s then S else 0
  have hs : (∑ u, wt u) = d^n*S := by
    unfold wt
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,card_fixed_symbol,Nat.cast_id]
  have hc : Fintype.card (Label (n+1) d) = d^(n+1) := by simp [Label]
  have h (u v : Label (n+1) d) :
      (if u i = s ∨ v i = s then S else 0) ≤ wt u + wt v := by
    unfold wt; split_ifs <;> omega
  have sum := Finset.sum_le_sum (s := univ) (fun u _ ↦ Finset.sum_le_sum (s := univ) (fun v _ ↦ h u v))
  change groupRaw S i s ≤ _ at sum
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc,
    ← Finset.mul_sum,hs,Nat.cast_id] at sum
  calc
    _ ≤ _ := Nat.mul_le_mul_right d sum
    _ = _ := by ring

end Cube

end BorderVNP
end Computability
end OAI
