import OAI.LinearAlgebra.FiniteFourier.IntegralGridInputs
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoJetCoordinates
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.JetOccupiedGridCircuit
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeConversionWord

/-! # Circuits for conversion on the grid of prime cyclic axes

The two half-length rows on each prime axis use at most thirteen spare
registers per data register. The occupied-fibers theorem synchronizes all
axes in this same space ratio on the full grid. Restricting each layer to
jet coordinates produces circuits on the two-local base.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace ConvolutionGrid

open Deformation Matrix Polynomial
open scoped BigOperators

/-- Linear gate budget for either direction of the prime-grid conversion. -/
noncomputable def atTwoPrimeGridCost (β C : ℝ) (B N e h s : ℕ) : ℝ :=
  let D : ℕ := 243 * (84 + 6400*(1 + Nat.clog 2 (2+B)))
  let V : ℝ := 14*N
  D * (V*(40*e*h*convolutionEnvelope s) + (2*e*h)*(C*V*(1+Real.logb 2 V)^β))

variable {σ : Type} [Fintype σ] [DecidableEq σ] {M h s B : ℕ} {β C : ℝ}

local notation "φ₂" => algebraMap TwoLocalBase TwoLocalQuadratic
local notation "ω₂" => AdjoinRoot.root (cyclotomic 3 TwoLocalBase)
local notation "J₂" => IntegralJet M h

variable {p : σ → ℕ} [∀ i, Fact (p i).Prime] {hM : Odd M}
  {hp : ∀ i, p i % 4 = 3} {h7 : ∀ i, 7 ≤ p i}

local notation "row" => fun i : σ => PrimeAxisRow ((p i-1)/2)
local notation "toJet" => algebraMap (CyclotomicCoefficients TwoLocalQuadratic M) J₂

/-- The protected forward and backward circuits on the complete prime grid. Their
wire labels retain the CRT residues on one side and the scalar/active row on the other. -/
theorem atTwo_primeGrid_circuits (a : ∀ i, AtTwoPrimeAxis M (p i) hM (hp i) (h7 i))
    (hle : ∀ i, (p i-1)/2 ≤ B) (h3 : ∀ j, 3^j ≤ 8*B → 3^j ∣ M) (hh : 0 < h)
    (hc : 2*M.totient*h ≤ s) (ht : IntegralShearBound β C) (hβ : 0 ≤ β) (hC : 0 ≤ C) :
    let cost := atTwoPrimeGridCost β C B (∏ i, p i) M.totient h s
    JetMatrixCircuit φ₂ ω₂ (cyclotomic M TwoLocalQuadratic) M.totient h
        (columns fun i => (a i).forward.map toJet) cost ∧
      JetMatrixCircuit φ₂ ω₂ (cyclotomic M TwoLocalQuadratic) M.totient h
        (columns fun i => (a i).backward.map toJet) cost := by
  classical
  let W (i : σ) := Bool × Fin (13*((p i-1)/2))
  let e (i : σ) := AtTwoPrimeAxis.rowAddress (p i) (hp i)
  have hn (i) : Fintype.card (row i) = p i := (Fintype.card_congr (e i)).trans (ZMod.card _)
  have hN : Fintype.card (∀ i, row i) = ∏ i, p i := by simp [Fintype.card_pi, hn]
  have ha (i) : 2 ≤ Fintype.card (row i) := by rw [hn]; exact le_trans (by decide) (h7 i)
  have hw (i) : Fintype.card (W i) ≤ Fintype.card (row i) * (14-1) := by
    simp only [W, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, hn]
    omega
  let := (AdjoinRoot.nontrivial_iff_of_monic (cyclotomic.monic 3 TwoLocalBase)).mpr
    (degree_cyclotomic_pos 3 _ (by decide))
  have compile {I O : σ → Type} [∀ i, Fintype (I i)] (A : ∀ i, Matrix (O i) (I i) J₂)
      (o : ∀ i, row i ≃ O i) (j : ∀ i, row i ≃ I i)
      (words : ∀ i, OccupiedWord (W i) (84 + 6400*(1+Nat.clog 2 (2+B)))
        ((A i).submatrix (o i) (j i))) :
      JetMatrixCircuit φ₂ ω₂ (cyclotomic M TwoLocalQuadratic) M.totient h (columns A)
        (atTwoPrimeGridCost β C B (∏ i, p i) M.totient h s) := by
    have q := occupiedGridMatrixCircuit A o j (by decide : 0 < 14) ha hw words
      (atTwoJetCircuitsOver hM.pos hh) atTwoCoefficientEncoding_bijective
      (cyclotomic.monic _ _) (natDegree_cyclotomic _ _) (Nat.totient_pos.mpr hM.pos) hh hc
      (ht.shearTensorBound TwoLocalBase) hβ hC
    simpa only [hN, occupiedGridJetCost, atTwoPrimeGridCost, show fiberDepthFactor 14 = 243 by decide,
      Nat.cast_ofNat] using q
  exact ⟨compile _ (fun _ => Equiv.refl _) e (fun i => ((a i).conversionWord h B (hle i) h3).1),
    compile _ e (fun _ => Equiv.refl _) (fun i => ((a i).conversionWord h B (hle i) h3).2)⟩

end ConvolutionGrid

end FiniteFourier
end LinearAlgebra
end OAI
