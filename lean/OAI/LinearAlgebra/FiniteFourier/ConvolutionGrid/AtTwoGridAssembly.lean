import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoGridTransform
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoEndpointSector
import OAI.LinearAlgebra.FiniteFourier.AtTwoCost.AtTwoPackedTransformCost
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.PackedAssemblyProduct

/-! # The complete pair of transforms for the two-local convolution grid -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace ConvolutionGrid

open Deformation Polynomial Matrix
open scoped BigOperators Classical

local notation "φ₂" => algebraMap TwoLocalBase TwoLocalQuadratic
local notation "ω₂" => AdjoinRoot.root (cyclotomic 3 TwoLocalBase)
local notation "O₂" => CyclotomicCoefficients TwoLocalQuadratic

variable {σ : Type} [Fintype σ] {p : σ → ℕ} [∀ i, Fact (p i).Prime]
  {M n r B s : ℕ} {β C : ℝ} {hM : Odd M} {hp : ∀ i, p i % 4 = 3} {h7 : ∀ i, 7 ≤ p i}

/-- The actual input and output circuits on all prime addresses. The same
input circuit is used for both operands. Its two evaluations and the decoder
satisfy the normalized work estimate simultaneously. -/
theorem assembleAtTwoGrid (a : ∀ i, AtTwoPrimeAxis M (p i) hM (hp i) (h7 i))
    (hwidth : ∀ i, (p i-1)/2 ≤ B) (h3 : ∀ k, 3^k ≤ 8*B → 3^k ∣ M)
    (hr : 0 < r) (hd : Fintype.card σ ≤ r)
    (hcH : 2*M.totient*(2*r+2*Fintype.card σ) ≤ s)
    (hNn : ∏ i, p i ≤ n) (hB : 6 ≤ B)
    (ht : IntegralShearBound β C) (hβ : 0 ≤ β) (hC : 0 ≤ C) :
    HasGridProductCircuits φ₂ ω₂ (cyclotomic M TwoLocalQuadratic) (∀ i, ZMod (p i)) M.totient r
      (fun _ : Σ S : Finset σ, ∀ i : S, Fin 2 × Fin ((p i.val-1)/2) =>
        2*r+2*Fintype.card σ)
      (3*(3*AtTwoCost.wordConstant C β+192)*(((∏ i, p i : ℕ):ℝ)*M.totient*r)*
        AtTwoCost.rate n r s B β) := by
  let H := 2*r+2*Fintype.card σ
  let e := M.totient
  let D := 6400*(1+Nat.clog 2 (2+B))
  let m (S : Finset σ) (i : S) := (p i.val-1)/2
  let ζ (S : Finset σ) (i : S) := (a i.val).jetRoot H
  let w := AtTwoCost.sectorWidth p
  let short (S : Finset σ) := atTwoWordCost e r (w S) s 37 β C
  let long (S : Finset σ) := atTwoWordCost e H (14*w S) s (243*D+37) β C
  let shift (S : Finset σ) (j : ℕ) := (w S : ℝ)*(8*(e : ℝ)*j*(1+Real.logb 2 j)*convolutionEnvelope s)
  let b (S : Finset σ) := short S + shift S r + long S
  let c (S : Finset σ) := long S + shift S H + short S
  let P := atTwoPrimeGridCost β C B (∏ i, p i) e r s
  have hrH : r ≤ H := by dsimp [H]; omega
  have hH : 0 < H := hr.trans_le hrH
  have hHr : H ≤ 4*r := by dsimp [H]; omega
  have he := Nat.totient_pos.mpr hM.pos
  have hs : 0 < s := (by positivity : 0 < 2*M.totient*H).trans_le hcH
  have hN : 0 < ∏ i, p i := Finset.prod_pos (fun i _ => by have := h7 i; omega)
  have hn := hN.trans_le hNn
  obtain ⟨hF,hV⟩ := atTwo_primeGrid_circuits a hwidth h3 hr
    ((Nat.mul_le_mul_left _ hrH).trans hcH) ht hβ hC
  choose T hprod hf hg using fun S => atTwo_sector_stages a r B s hr S hwidth h3 hcH ht hβ hC
  let f (S : Finset σ) := (T S).input (m S) (ζ S)
  let g (S : Finset σ) := (T S).output (m S) (ζ S)
  have hbc (S : Finset σ) := by
    obtain ⟨hw,hwn⟩ := AtTwoCost.atTwoSector_card_pos_le p hp S
    exact AtTwoCost.endpointCosts_le (e := e) hn hs hB hβ hC hw (hwn.trans hNn)
      hr hH hHr (le_rfl : D ≤ _)
  have hw := AtTwoCost.weighted_cost_le p hp hN hNn hn hs hB hβ hC
    (le_rfl : P ≤ _) (le_rfl : P ≤ _) (b := b) (c := c) (fun S => (hbc S).1) (fun S => (hbc S).2)
  have h := exists_sectorProductCircuits (sectorEquiv (K := fun i => Fin 2 × Fin ((p i-1)/2)))
    hF hV (f := f) (g := g) (b := b) (c := c) hf hg (by
      intro x y z hz
      apply atTwo_grid_recover a (algebraMap (O₂ M) (IntegralJet M r)) x y z
      intro S
      exact (hz S).trans (hprod S _ _))
  obtain ⟨u,v,q,t,inMap,outMap,hprice,hq,ht',hprod'⟩ := h
  exact ⟨u,v,q,t,inMap,outMap,hprice.trans hw,hq,ht',hprod'⟩

end ConvolutionGrid

end FiniteFourier
end LinearAlgebra
end OAI
