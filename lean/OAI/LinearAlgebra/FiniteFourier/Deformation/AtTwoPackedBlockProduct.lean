import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoBlockProduct
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeAxis
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoGridProduct

/-! # The actual active prime blocks over the two-local cyclotomic jets

Each subset uses the same long height and the roots of its chosen prime-axis
presentations. Its transforms recover exactly the product table used by the
prime-grid convolution in this sector.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial
open scoped BigOperators Classical

private theorem eval_integralCoeff_atOne {R A σ : Type*} [CommRing R] [CommRing A] [Fintype σ]
    (φ : R →+* A) (ρ β : σ → R) (m : σ → ℕ) (a b k : Address m) :
    φ ((integralCoeff ρ β m a b k).eval 1) =
      ConvolutionGrid.coeff (fun i => primeAxisActiveCoeff (m := m i) (φ (ρ i)) (φ (β i))) a b k := by
  simp only [integralCoeff, eval_prod, map_prod, ConvolutionGrid.coeff]
  apply Finset.prod_congr rfl
  intro i _
  simp only [primeAxisActiveCoeff, quadraticCoeff, binomialCoeff, binomial, eval_mul]
  split_ifs <;> simp

local notation "O₂" => CyclotomicCoefficients TwoLocalQuadratic

variable {σ : Type*} [Fintype σ] {M : ℕ} {p : σ → ℕ} [∀ i, Fact (p i).Prime]
  {hM : Odd M} {hp : ∀ i, p i % 4 = 3} {h7 : ∀ i, 7 ≤ p i}
  (a : ∀ i, AtTwoPrimeAxis M (p i) hM (hp i) (h7 i))

/-- The axis generator extended to the long jet in the same coefficient tower. -/
noncomputable def AtTwoPrimeAxis.jetRoot {p : ℕ} [Fact p.Prime] {M : ℕ} {hM : Odd M}
    {hp : p % 4 = 3} {h7 : 7 ≤ p} (a : AtTwoPrimeAxis M p hM hp h7) (H : ℕ) :
    (IntegralJet M H)ˣ := Units.map (algebraMap (O₂ M) (IntegralJet M H)) a.root

theorem AtTwoPrimeAxis.jetRoot_eq {p : ℕ} [Fact p.Prime] {M : ℕ} {hM : Odd M}
    {hp : p % 4 = 3} {h7 : 7 ≤ p} (a : AtTwoPrimeAxis M p hM hp h7) (H : ℕ) :
    (a.jetRoot H : IntegralJet M H) = (jetCyclotomicCoordinate M H)^(M/((p-1)/2)) := by
  change algebraMap (O₂ M) _ (a.root : O₂ M) = _
  rw [a.root_eq, map_pow]
  rfl

/-- The nonscalar subproduct has common split-point transforms whose multiplication
law is the cyclic grid's actual sector law. The empty subset is included. -/
theorem exists_atTwoSectorTransforms (r : ℕ) (hr : 0 < r) (S : Finset σ) :
    let H := 2*r + 2*Fintype.card σ
    let φ := algebraMap (O₂ M) (IntegralJet M r)
    let m := fun i : S => (p i.val-1)/2
    let ζ := fun i : S => (a i.val).jetRoot H
    ∃ T : BlockProductTransforms (O₂ M) S r H,
      (∀ i, Pairwise fun j k => IsUnit (T.quadraticNodes i j - T.quadraticNodes i k)) ∧
      ∀ x y, T.output m ζ (T.input m ζ x * T.input m ζ y) =
        multiply (ConvolutionGrid.coeff fun i : S => primeAxisActiveCoeff (m := m i)
          (φ (((p i.val + 1)/4 : ℕ) : O₂ M)) (φ ((a i.val).beta : O₂ M))) x y := by
  classical
  intro H φ m ζ
  let := atTwoJet_nontrivial hM.pos hr
  let ρ (i : S) : O₂ M := ((p i.val + 1)/4 : ℕ)
  let β (i : S) : (O₂ M)ˣ := (a i.val).beta
  let g := algebraMap (O₂ M) (IntegralJet M H)
  have hwidth (i : S) (l : ℕ) := (primeAxis_jet_units M l (hp i.val)).2.1
  have hdisc (i : S) : IsUnit (1 - 4 * φ (ρ i)) := by
    simpa [φ, ρ] using (primeAxis_jet_units M r (hp i.val)).2.2
  have hζ (i : S) : (ζ i)^(m i) = 1 := by
    simp only [ζ, AtTwoPrimeAxis.jetRoot, m, ← map_pow, AtTwoPrimeAxis.root_pow, map_one]
  have hsep (i : S) : Pairwise fun j k : Fin (m i) =>
      IsUnit ((ζ i : IntegralJet M H)^j.val - (ζ i : IntegralJet M H)^k.val) := by
    intro j k hjk
    simpa [ζ, AtTwoPrimeAxis.jetRoot, g] using ((a i.val).separated j k hjk).map g
  have hm (i : S) : 0 < m i := by dsimp [m]; have := h7 i.val; omega
  obtain ⟨T, hu, he⟩ := exists_blockProductTransforms r (Fintype.card σ) hr
    (Fintype.card_le_of_injective Subtype.val Subtype.val_injective) ρ β m hm
    (fun i => hwidth i r) hdisc ζ hζ (fun i => hwidth i H) hsep
  refine ⟨T, hu, fun x y => ?_⟩
  rw [he]
  simp only [eval_integralCoeff_atOne]
  rfl

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
