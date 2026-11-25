import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.JetOccupiedGridCircuit
import OAI.LinearAlgebra.FiniteFourier.AtTwoCost.AtTwoCost
import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicDeformationCircuits
import OAI.LinearAlgebra.FiniteFourier.PrimeJetPacking.DyadicPackedAssemblyCost

/-! # Costs of dyadic deformation at the two jet centers

In each direction a sector uses one Taylor shift, one short-jet scaling, and
one long-jet scaling. The degree-volume bound controls their total over all
sectors, including the sector with no active axes.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Real Deformation.Dyadic

/-- Charge both scalings and the shift to the short jet's coefficient count.
The combined heights in either direction are at most four times the short height. -/
theorem dyadic_endpointCost_le {n e r h H W s : ℕ} {B β : ℝ} (hn : 0 < n) (hB : 1 ≤ B)
    (hh : 0 < h) (hmax : h+H ≤ 4*r) (hs : 0 < s) :
    endpointCost W e h H s ≤ 352*((W:ℝ)*e*r)*AtTwoCost.rate n r s B β := by
  let q := AtTwoCost.rate n r s B β
  have hE := AtTwoCost.envelope_le_rate (β := β) (r := r) hn hs hB
  have hT := AtTwoCost.taylor_le (e := e) (v := W) (β := β) hn hh
    (show h ≤ 4*r by omega) hs hB
  have hE₀ := zero_le_one.trans (convolutionEnvelope_one_le hs)
  have hscale : (W:ℝ)*(40*e*(h+H))*convolutionEnvelope s ≤ 160*(W*e*r)*q := by
    calc
      _ ≤ (W:ℝ)*(40*e*(4*r))*q := by
        have hmax' : (h:ℝ)+H ≤ 4*r := by exact_mod_cast hmax
        dsimp only [q]; gcongr
      _ = _ := by ring
  unfold endpointCost
  dsimp only [q] at hscale
  linarith only [hscale, hT]

namespace PrimeJetPacking

variable {P : Finset ℕ} {n e : ℕ} {B β : ℝ} (pack : PrimeJetPacking P n e B)

/-- Data width of a sector in the packed dyadic list. -/
abbrev dyadicSectorWidth (S : Finset pack.axes) := Fintype.card (∀ i : S, Fin (i.val.val-1))

theorem sum_dyadicSectorWidth (hp : ∀ p ∈ pack.axes, 0 < p) :
    ∑ S, pack.dyadicSectorWidth S = ∏ p ∈ pack.axes, p := by
  simpa only [DyadicPoint, Fintype.card_sigma] using pack.card_dyadicPoint hp

/-- Total charge for the two inputs and one output, leaving the Fourier stages'
costs explicit. The constant is independent of the list and of the shear exponent. -/
theorem dyadic_endpointCosts_le (hn : 0 < n) (hB : 1 ≤ B)
    (hp : ∀ p ∈ pack.axes, 0 < p) (s : ℕ) (hs : 0 < s)
    (inp out : Finset pack.axes → ℝ) :
    let r := pack.jet
    let H (S : Finset pack.axes) := 2*r + S.card
    2*(∑ S, (inp S + endpointCost (pack.dyadicSectorWidth S) e r (H S) s)) +
      (∑ S, (out S + endpointCost (pack.dyadicSectorWidth S) e (H S) r s)) ≤
      2*(∑ S, inp S) + (∑ S, out S) + pack.widthWork 9504 β s := by
  intro r H
  let q := AtTwoCost.rate n r s B β
  have hr : 0 < r := by
    have h : (1:ℝ) ≤ r := hB.trans pack.jet_lower
    exact_mod_cast h
  have hmax (S : Finset pack.axes) : r + H S ≤ 4*r := by
    have := pack.dyadicHeight_le S
    change r + (2*r+S.card) ≤ 4*r
    dsimp [r] at *
    omega
  have hOne (i : Bool) :
      (∑ S, endpointCost (pack.dyadicSectorWidth S) e (if i then r else H S)
        (if i then H S else r) s) ≤ 352*(9*n)*q := by
    calc
      _ ≤ ∑ S, 352*((pack.dyadicSectorWidth S:ℝ)*e*r)*q := by
        apply Finset.sum_le_sum
        intro S _
        apply dyadic_endpointCost_le hn hB _ _ hs
        · cases i <;> dsimp [H] <;> omega
        · cases i <;> simpa only [Bool.false_eq_true, ↓reduceIte, add_comm (H S)] using hmax S
      _ = ((∑ S, pack.dyadicSectorWidth S : ℕ):ℝ)*(352*e*r*q) := by
        push_cast
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ _ := by
        rw [pack.sum_dyadicSectorWidth hp]
        have hv : ((∏ p ∈ pack.axes, p : ℕ):ℝ)*e*r ≤ 9*n := by exact_mod_cast pack.volume_upper
        have hq : 0 ≤ q := (zero_le_one.trans (convolutionEnvelope_one_le hs)).trans
          (AtTwoCost.envelope_le_rate hn hs hB)
        nlinarith only [mul_le_mul_of_nonneg_right hv hq]
  have h₁ := hOne true
  have h₂ := hOne false
  simp only [Bool.false_eq_true, ↓reduceIte] at h₁ h₂
  have hW : pack.widthWork 9504 β s = 9504*n*q := by
    unfold widthWork q AtTwoCost.rate
    ring
  rw [hW]
  simp only [Finset.sum_add_distrib]
  linarith only [h₁, h₂]

/-- Combine the whole-grid transforms, the Fourier transforms on the individual
sectors, and the two local endpoint operations on each path. -/
theorem dyadic_transformCosts_le (hn : 0 < n) (hB : 1 ≤ B)
    (hp : ∀ p ∈ pack.axes, 0 < p) {s : ℕ} (hs : 0 < s)
    (inp out : Finset pack.axes → ℝ) {cf cb C₁ C₂ : ℝ}
    (hprime : 2*cf+cb ≤ pack.widthWork C₁ β s)
    (hfourier : ∑ S, (2*inp S + out S) ≤ pack.widthWork C₂ β s) :
    let r := pack.jet
    let H (S : Finset pack.axes) := 2*r + S.card
    2*cf + cb + ∑ S, (2*(inp S + endpointCost (pack.dyadicSectorWidth S) e r (H S) s) +
      (out S + endpointCost (pack.dyadicSectorWidth S) e (H S) r s)) ≤
      pack.widthWork (C₁+C₂+9504) β s := by
  intro r H
  have h := pack.dyadic_endpointCosts_le (β := β) hn hB hp s hs inp out
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hfourier ⊢
  have hW : pack.widthWork (C₁+C₂+9504) β s =
      pack.widthWork C₁ β s + pack.widthWork C₂ β s + pack.widthWork 9504 β s := by
    unfold widthWork
    ring
  rw [hW]
  change 2*(∑ S, (inp S + endpointCost (pack.dyadicSectorWidth S) e r (H S) s)) +
    (∑ S, (out S + endpointCost (pack.dyadicSectorWidth S) e (H S) r s)) ≤ _ at h
  simp only [Finset.sum_add_distrib] at h
  linarith only [h, hprime, hfourier]

/-- The synchronized endpoint words work on fourteen registers per data entry.
Summing the three transforms over all sectors charges the packing volume once
per transform, for a total multiplier of at most twenty-seven. -/
theorem dyadic_fourierCosts_le {B : ℕ} (pack : PrimeJetPacking P n e B)
    (hn : 0 < n) (hB : 6 ≤ B) (hp : ∀ p ∈ pack.axes, 2 ≤ p)
    {s : ℕ} (hs : 0 < s) {C : ℝ} (hC : 0 ≤ C) (hβ : 0 ≤ β) :
    let F (S : Finset pack.axes) := ConvolutionGrid.occupiedGridJetCost β C 14
      (6400*(1+Nat.clog 2 (2+B))) (pack.dyadicSectorWidth S) e (2*pack.jet+S.card) s
    ∑ S, (2*F S+F S) ≤ pack.widthWork (27*AtTwoCost.wordConstant C β) β s := by
  intro F
  let q := AtTwoCost.rate n pack.jet s B β
  let c := AtTwoCost.wordConstant C β
  have hq : 0 ≤ q := (zero_le_one.trans (convolutionEnvelope_one_le hs)).trans
    (AtTwoCost.envelope_le_rate hn hs (by exact_mod_cast (show 1 ≤ B by omega)))
  have hc : 0 ≤ c := AtTwoCost.wordConstant_nonneg hC
  have hcard := pack.sum_dyadicSectorWidth (fun p h => by have := hp p h; omega)
  have hloc (S : Finset pack.axes) : F S ≤ c*((pack.dyadicSectorWidth S:ℝ)*e*pack.jet)*q := by
    have hnS : pack.dyadicSectorWidth S ≤ n :=
      ((Finset.single_le_sum (fun i _ => Nat.zero_le (pack.dyadicSectorWidth i))
        (Finset.mem_univ S)).trans hcard.le).trans pack.product_le
    have hpos : 0 < pack.dyadicSectorWidth S := Fintype.card_pos_iff.mpr
      ⟨fun i => ⟨0, by have := hp i.val.val i.val.property; omega⟩⟩
    have hD : fiberDepthFactor 14 = 243 := by decide
    simpa only [F, ConvolutionGrid.occupiedGridJetCost, Nat.cast_mul, Nat.cast_ofNat, hD] using
      AtTwoCost.stage_le (C := C) (e := e) (W := 14*pack.dyadicSectorWidth S)
        (D := fiberDepthFactor 14 * (6400*(1+Nat.clog 2 (2+B)))) hn hs hB hβ hC hnS
        (by positivity) le_rfl ((pack.dyadicHeight_le S).trans (by omega)) (by rw [hD]; omega)
  have hW : pack.widthWork (27*c) β s = (27*c)*n*q := by unfold widthWork q AtTwoCost.rate; ring
  change _ ≤ pack.widthWork (27*c) β s
  rw [hW]
  calc
    _ ≤ ∑ S, ((pack.dyadicSectorWidth S:ℝ)*(3*c*e*pack.jet*q)) := by
      exact Finset.sum_le_sum fun S _ => by linarith only [hloc S]
    _ = ((∏ p ∈ pack.axes, p : ℕ):ℝ)*(3*c*e*pack.jet*q) := by
      rw [← Finset.sum_mul, ← hcard]; push_cast; rfl
    _ ≤ _ := by
      have hv : ((∏ p ∈ pack.axes, p : ℕ):ℝ)*e*pack.jet ≤ 9*n := by exact_mod_cast pack.volume_upper
      nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hc) hq]

end PrimeJetPacking

end FiniteFourier
end LinearAlgebra
end OAI
