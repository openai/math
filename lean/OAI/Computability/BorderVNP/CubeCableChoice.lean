import OAI.Computability.BorderVNP.CubeLabelChoice
import OAI.Computability.BorderVNP.CubePublicLabels

/-!
# Compressed cable labels and their bitwise loads

The public label scan runs on weighted descriptors. Expanding a descriptor of width
`w` into `w` bit indicators gives the identical objective. This identifies the
executable scan's output with the labeling satisfying Lemma 8.2.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Balancing

open Finset
open scoped BigOperators

variable {C E A : Type*} [Fintype C] [DecidableEq C] [Fintype E] [DecidableEq E]
  [Fintype A] [DecidableEq A] {z : ℕ}

/-- Individual bit positions of compressed public descriptors. -/
abbrev Bits {I : Type*} (w : I → ℕ) := (i : I) × Fin (w i)

/-- All ordered cable and incoming-data bins of the public label scan.
Unused descriptor kinds have zero width and empty support. -/
def labelBins (src dst : E → C) (recv : A → C) (w : E → ℕ) (v : A → ℕ) :
    (Fin (z+1) × Fin (z+1)) ⊕ Fin (z+1) → Bin C (Fin (z+1)) (E ⊕ A)
  | .inl (u,t) =>
    ⟨Sum.elim (cable src dst u t) (fun _ ↦ ⟨∅, fun _ ↦ u⟩),
     Sum.elim (fun e ↦ w e) (fun _ ↦ 0), Fintype.card (Bits w)/(z+1 : ℚ)^2⟩
  | .inr u =>
    ⟨Sum.elim (fun _ ↦ ⟨∅,fun _ ↦ u⟩) (datum recv u),
     Sum.elim (fun _ ↦ 0) (fun a ↦ v a), Fintype.card (Bits v)/(z+1 : ℚ)⟩

/-- Summing over individual bits of a descriptor is multiplication by its width. -/
theorem sum_bits {I : Type*} [Fintype I] (w : I → ℕ) (f : I → ℝ) :
    (∑ i : Bits w, f i.1) = ∑ i : I, (w i : ℝ)*f i := by
  rw [Fintype.sum_sigma]; simp

omit [DecidableEq E] [DecidableEq A] in
/-- The objective computed from compressed descriptors equals the true bitwise objective. -/
theorem labelBins_deviation (src dst : E → C) (recv : A → C) (w : E → ℕ) (v : A → ℕ) :
    binDeviation (labelBins (z := z) src dst recv w v) =
      deviation (L := Fin (z+1)) (fun b : Bits w ↦ src b.1) (fun b ↦ dst b.1)
        (fun b : Bits v ↦ recv b.1) := by
  funext x
  rw [binDeviation,deviation,Fintype.sum_sum_type]
  simp only [labelBins,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Rat.cast_natCast,
    Rat.cast_zero,zero_mul,Finset.sum_const_zero,add_zero,zero_add,Rat.cast_div,Rat.cast_pow,
    Rat.cast_add,Rat.cast_one,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  congr 1
  · apply Finset.sum_congr rfl; intro p _
    rw [load]
    change ((∑ e, (w e : ℝ)*hit (cable src dst p.1 p.2 e) x)-_)^2 =
      ((∑ e : Bits w, hit (cable src dst p.1 p.2 e.1) x)-_)^2
    rw [sum_bits w (fun e ↦ hit (cable src dst p.1 p.2 e) x)]
  · apply Finset.sum_congr rfl; intro u _
    rw [load]
    change ((∑ a, (v a : ℝ)*hit (datum recv u a) x)-_)^2 =
      ((∑ a : Bits v, hit (datum recv u a.1) x)-_)^2
    rw [sum_bits v (fun a ↦ hit (datum recv u a) x)]

/-- The public executable labeling operating on weighted cable and data descriptors
meets the simultaneous bit-load bounds of Lemma 8.2. -/
theorem public_labels_balanced (src dst : E → C) (recv : A → C) (w : E → ℕ) (v : A → ℕ)
    (cs : List C) (hcs : cs.toFinset = univ) (W : ℝ) (M : ℕ)
    (hne : ∀ e, src e ≠ dst e)
    (hcable : (Fintype.card (Bits w) : ℝ) ≤ 2*W) (hdata : (Fintype.card (Bits v) : ℝ) ≤ W)
    (hE : ∀ c, (univ.filter (fun b : Bits w ↦ c ∈ ({src b.1,dst b.1} : Finset C))).card ≤ M)
    (hA : ∀ c, (univ.filter (fun b : Bits v ↦ c = recv b.1)).card ≤ M)
    (hbudget : (z+1 : ℝ)^2 * (4*W*M) + (z+1)*(W*M) ≤ (W/(z+1 : ℝ)^2)^2) :
    let bins := labelBins (z := z) src dst recv w v
    let x := publicLabels bins (fun j ↦ index (bins j)) cs ∅ (fun _ ↦ 0)
      (initialMoments bins ∅ (fun _ ↦ 0))
    (∀ u t, load (cable (fun b : Bits w ↦ src b.1) (fun b ↦ dst b.1) u t) x ≤
      4*W/(z+1 : ℝ)^2) ∧
      ∀ u, load (datum (fun b : Bits v ↦ recv b.1) u) x ≤ 4*W/(z+1 : ℝ) := by
  dsimp only
  rw [publicLabels_eq,labelBins_deviation]
  exact chosen_labels_balanced _ _ _ _ cs hcs W M (fun b ↦ hne b.1) hcable hdata hE hA hbudget

end Cube.Balancing

end BorderVNP
end Computability
end OAI
