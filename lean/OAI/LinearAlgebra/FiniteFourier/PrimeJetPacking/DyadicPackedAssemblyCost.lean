import OAI.LinearAlgebra.FiniteFourier.PackedParameters
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoGridProduct
import OAI.LinearAlgebra.FiniteFourier.JetOpenAssembly
import OAI.LinearAlgebra.FiniteFourier.AtTwoCost.AtTwoCost

/-! # The volume and linear work of the split products in a protected list -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace PrimeJetPacking

open Real
open scoped BigOperators

variable {P L : Finset ℕ} {n e : ℕ} {B C β : ℝ} (pack : PrimeJetPacking P n e B)

/-- A split point records the active prime axes and one non-scalar frequency on
each of them. This includes one point for the sector with no active axes. -/
abbrev DyadicPoint := Σ S : Finset pack.axes, (i : S) → Fin (i.val.val - 1)

theorem card_dyadicPoint (hp : ∀ p ∈ pack.axes, 0 < p) :
    Fintype.card pack.DyadicPoint = ∏ p ∈ pack.axes, p := by
  classical
  rw [Fintype.card_congr (ConvolutionGrid.sectorEquiv (K := fun i : pack.axes => Fin (i.val-1))),
    Fintype.card_pi, ← Finset.prod_coe_sort pack.axes (fun p => p)]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Fintype.card_option, Fintype.card_fin]
  have := hp i.val i.property
  omega

/-- The recovery threshold at a sector never exceeds three times the input jet height. -/
theorem dyadicHeight_le (S : Finset pack.axes) : 2*pack.jet + S.card ≤ 3*pack.jet := by
  have h : pack.axes.card ≤ pack.jet := by exact_mod_cast pack.axes_le.trans pack.jet_lower
  have hS := S.card_le_univ
  rw [Fintype.card_coe] at hS
  omega

/-- Add the gather and the local jet encoders and decoders to the two input
transforms and the output transform. The child-length factor is six for
the dyadic list (`k=3`) and eight for the at-two list (`k=4`). -/
theorem protectedList_of_jetBlockCost {J : Type} [Fintype J]
    (hn : 0 < n) (hB : 1 ≤ B) {k : ℕ} (hk : 0 < k)
    (hcard : Fintype.card J = ∏ p ∈ pack.axes, p)
    (h : J → ℕ) (hh : ∀ j, 0 < h j ∧ h j ≤ k*pack.jet) {a d : ℕ}
    (q : OpenConvolution (protectedRationals L) n (J × Fin 3) (jetBlockLength (fun _ => e) h))
    (hq : q.RealizesMultiple 1)
    (hcost : q.linearCost ≤ 2*a+d+e*pack.jet*(∏ p ∈ pack.axes, p) +
      ∑ j, JetAssembly.blockCost e (h j))
    (htrans : ((2*a+d : ℕ) : ℝ) ≤ pack.widthWork C β (pack.childCutoff (2*k))) :
    ProtectedPackedList n L (3*(2*k)*(9*n)) (pack.childCutoff (2*k))
      (pack.widthWork (C+9+324*k) β (pack.childCutoff (2*k))) := by
  have hv : 0 < (∏ p ∈ pack.axes, p) * e * pack.jet :=
    (by omega : 0 < 8*n).trans_le pack.volume_lower
  have he : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at hv)
  have hr : 0 < pack.jet := Nat.pos_of_ne_zero (by intro hz; simp [hz] at hv)
  let s := pack.childCutoff (2*k)
  have hes : e ≤ s := by
    change e ≤ (2*k)*e*pack.jet
    calc
      e ≤ (2*k)*e := Nat.le_mul_of_pos_left e (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_right _ hr
  refine ⟨_, inferInstance, _, q, hq, ?_,
    JetAssembly.sum_childLength_le_of_packing pack hcard h (fun j => (hh j).2), ?_⟩
  · intro j
    change 0 < 2*e*h j.1 ∧ 2*e*h j.1 ≤ (2*k)*e*pack.jet
    refine ⟨by have := (hh j.1).1; positivity, ?_⟩
    exact (Nat.mul_le_mul_left (2*e) (hh j.1).2).trans_eq (by ring)
  · have hc := JetAssembly.sum_blockCost_div_le_of_packing pack hn he hes hcard h (fun j => (hh j).2)
    have hc' := (div_le_iff₀ (by exact_mod_cast hn : 0 < (n:ℝ))).mp hc
    let W := (1+log B)^2 * ((1+logb 2 n)^β + (1+log (2+pack.jet))*convolutionEnvelope s)
    have hEW : convolutionEnvelope s ≤ W := AtTwoCost.envelope_le_rate hn (he.trans_le hes) hB
    have hW := (convolutionEnvelope_one_le (he.trans_le hes)).trans hEW
    have hvol : e*pack.jet*(∏ p ∈ pack.axes, p) ≤ 9*n := by
      simpa only [mul_rotate] using pack.volume_upper
    have hcost' : (q.linearCost : ℝ) ≤ ((2*a+d : ℕ):ℝ) + 9*n +
        ((∑ j, JetAssembly.blockCost e (h j) : ℕ):ℝ) := by
      exact_mod_cast hcost.trans (Nat.add_le_add_right (Nat.add_le_add_left hvol _) _)
    have hgather := mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ 9*(n:ℝ))
    have hblock := mul_le_mul_of_nonneg_left hEW (by positivity : 0 ≤ 324*(k:ℝ)*n)
    change ((2*a+d : ℕ):ℝ) ≤ C*n*(1+log B)^2*_ at htrans
    change _ ≤ (C+9+324*(k:ℝ))*n*(1+log B)^2*_
    dsimp only [W,s] at hW hEW hgather hblock hc'
    linarith only [hcost', htrans, hc', hgather, hblock]

/-- The split products on all the dyadic sectors give the required protected
list. In addition to the transform work, 981 times the width factor covers
the packing gather and every jet decoder and encoder. -/
theorem protectedList_of_dyadicSectors (hn : 0 < n) (hB : 1 ≤ B)
    (hp : ∀ p ∈ pack.axes, 0 < p) {a d : ℕ}
    (q : OpenConvolution (protectedRationals L) n (pack.DyadicPoint × Fin 3)
      (jetBlockLength (fun _ => e) (fun j => 2*pack.jet + j.1.card)))
    (hq : q.RealizesMultiple 1)
    (hcost : q.linearCost ≤ 2*a+d+e*pack.jet*(∏ p ∈ pack.axes, p) +
      ∑ j : pack.DyadicPoint, JetAssembly.blockCost e (2*pack.jet+j.1.card))
    (htrans : ((2*a+d : ℕ) : ℝ) ≤ pack.widthWork C β (pack.childCutoff 6)) :
    ProtectedPackedList n L (3*6*(9*n)) (pack.childCutoff 6)
      (pack.widthWork (C+981) β (pack.childCutoff 6)) := by
  have hr : 0 < pack.jet := by
    have h := (by omega : 0 < 8*n).trans_le pack.volume_lower
    exact Nat.pos_of_ne_zero fun hz => by simp [hz] at h
  have H := pack.protectedList_of_jetBlockCost hn hB (k := 3) (by decide)
    (pack.card_dyadicPoint hp) (fun j => 2*pack.jet+j.1.card)
    (fun j => ⟨by positivity, pack.dyadicHeight_le j.1⟩) q hq hcost htrans
  convert H using 2
  norm_num
  ring

end PrimeJetPacking

end FiniteFourier
end LinearAlgebra
end OAI
