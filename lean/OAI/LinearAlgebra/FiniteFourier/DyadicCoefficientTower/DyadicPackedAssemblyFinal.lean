import OAI.LinearAlgebra.FiniteFourier.DyadicCoefficientTower.DyadicCoefficientsAxis
import OAI.LinearAlgebra.FiniteFourier.DyadicCoefficientTower.DyadicCoefficientsBasis
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.DyadicPackedAssembly
import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicPackedAssemblyStages
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.DyadicPackedAssemblyProduct
import OAI.LinearAlgebra.FiniteFourier.DyadicTransformCost

/-! # The protected dyadic open list from its Fourier circuits -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace DyadicCoefficientTower

open Deformation ConvolutionGrid Polynomial Matrix
open scoped Classical BigOperators

private theorem changeJetFintype {R S I O : Type*} [CommRing R] [CommRing S]
    {φ : R →+* S} {η : S} {M : S[X]} {e h : ℕ}
    {A : Matrix O I (JetQuotient M h)} {c : ℝ} {i j : Fintype I}
    (H : @JetMatrixCircuit R S _ _ φ η M e h I O i A c) :
    @JetMatrixCircuit R S _ _ φ η M e h I O j A c := (Subsingleton.elim i j) ▸ H

private theorem changeCyclicProduct {R G : Type*} [CommRing R] [Add G]
    {i j : Fintype G} {d d' : DecidableEq G} {x y z : G → R}
    (H : z = @cyclicProduct R _ G i _ d x y) : z = @cyclicProduct R _ G j _ d' x y := by
  cases Subsingleton.elim i j
  cases Subsingleton.elim d d'
  exact H

private theorem changeGridFintype {R S G K : Type*} [CommRing R] [CommRing S] [Add G]
    {i j : Fintype G} {d d' : DecidableEq G} {φ : R →+* S} {η : S} {M : S[X]}
    {e r : ℕ} {H : K → ℕ} {c : ℝ}
    (h : @HasGridProductCircuits R S K _ _ φ η M G i _ d e r H c) :
    @HasGridProductCircuits R S K _ _ φ η M G j _ d' e r H c := by
  cases Subsingleton.elim i j
  cases Subsingleton.elim d d'
  exact h

private theorem changeProductFintype {J A : Type*} [CommRing A] {i j : Fintype J}
    {c : J → J → J → A} {x y z : J → A} (h : z = @multiply J A i _ c x y) :
    z = @multiply J A j _ c x y := (Subsingleton.elim i j) ▸ h

variable {η β C₁ C₂ : ℝ} {n B : ℕ} {D : DyadicAxisPacking GaussianRationals η n B}
  {L : Finset ℕ} (T : DyadicCoefficientTower D L) [Nontrivial T.Order]
  [∀ i : D.packing.axes, Fact i.val.Prime]

local notation "σ" => Subtype (fun p => p ∈ D.packing.axes)
local notation "e" => listCyclotomicDegree GaussianRationals D.pool B
local notation "r" => D.packing.jet
local notation "cut" => D.packing.childCutoff 6
local notation "φ" => algebraMap (protectedRationals L) (protectedGaussian L)
local notation "η₀" => protectedGaussianI L
local notation "width" => fun (S : Finset σ) (i : S) => Subtype.val (Subtype.val i) - 1
local notation "long" => fun S : Finset σ => 2*r + Finset.card S
local notation "rootNodes" => fun (S : Finset σ) (i : S) (j : Fin (width S i)) =>
  (T.axisRoot (Subtype.property (Subtype.val i)) : T.Order)^(Fin.val j)

set_option maxHeartbeats 300000 in
/-- In one dyadic protected list, a prime-grid transform and one Fourier transform
on each sector implement the whole common-encoder convolution. The constant 10485
accounts for the jet shifts, fixed multipliers, local encoders, and gathering. -/
theorem protectedList_of_fourierCircuits (hn : 0 < n) {cf cb : ℝ} {af ab : Finset σ → ℝ}
    (pf : JetMatrixCircuit φ η₀ T.modulus e r
      (columns fun i : σ => (T.primeAxis i.property).forward.map
        (algebraMap T.Order (JetQuotient T.modulus r))) cf)
    (pb : JetMatrixCircuit φ η₀ T.modulus e r
      (columns fun i : σ => (T.primeAxis i.property).backward.map
        (algebraMap T.Order (JetQuotient T.modulus r))) cb)
    (sf : ∀ S : Finset σ, JetMatrixCircuit φ η₀ T.modulus e (long S)
      ((Dyadic.evaluation (width S) (rootNodes S)).map
        (algebraMap T.Order (JetQuotient T.modulus (long S)))) (af S))
    (sb : ∀ S : Finset σ, JetMatrixCircuit φ η₀ T.modulus e (long S)
      ((Dyadic.interpolation (width S) (rootNodes S)).map
        (algebraMap T.Order (JetQuotient T.modulus (long S)))) (ab S))
    (hprime : 2*cf+cb ≤ D.packing.widthWork C₁ β cut)
    (hfourier : ∑ S, (2*af S+ab S) ≤ D.packing.widthWork C₂ β cut) :
    ProtectedPackedList n L (3*6*(9*n)) cut (D.packing.widthWork (C₁+C₂+10485) β cut) := by
  have he : 0 < e := degree_pos
  have hB : 1 ≤ (B : ℝ) := by exact_mod_cast (by have := T.width; omega : 1 ≤ B)
  have hr : 0 < r := by exact_mod_cast (zero_lt_one.trans_le (hB.trans D.packing.jet_lower))
  have hlong (S : Finset σ) : 0 < long S := by dsimp; omega
  have hs : 0 < cut := D.packing.childCutoff_pos hn (by decide)
  have hp (p : ℕ) (hp : p ∈ D.packing.axes) : 0 < p := (T.axis_prime hp).pos
  have support (S : Finset σ) : 2*e*(long S) ≤ cut :=
    (Nat.mul_le_mul_left (2*e) (D.packing.dyadicHeight_le S)).trans_eq (by
      change 2*e*(3*r) = 6*e*r
      ring)
  have split (S : Finset σ) := Dyadic.exists_productStages («σ» := S) («r» := r) (s := cut)
    (H := long S) (Cf := af S) (Cb := ab S) (width S)
    (fun i : S => (T.primeAxis i.val.property).beta)
    (fun i => T.axisPredecessorUnit i.val.property) (fun i => T.axisRoot i.val.property)
    (fun i => T.axisRoot_pow i.val.property) (fun i => T.axisRoot_separate i.val.property)
    (protectedGaussian_coordinates L) T.monic T.degree_eq he hr (fun _ hh => T.jets hh)
    (by rw [Fintype.card_coe]) (support S) (sf S) (sb S)
  choose f j hf hj hmul using split
  let costF (S : Finset σ) := af S + Dyadic.endpointCost (D.packing.dyadicSectorWidth S) e r (long S) cut
  let costB (S : Finset σ) := ab S + Dyadic.endpointCost (D.packing.dyadicSectorWidth S) e (long S) r cut
  have grid : HasGridProductCircuits φ η₀ T.modulus (∀ i : σ, ZMod i.val) e r
      (fun k : D.packing.DyadicPoint => long k.1) (2*cf+cb+∑ S, (2*costF S+costB S)) := by
    have aux := exists_dyadicGridCircuits (p := fun i : σ => i.val)
      (C := fun i => T.axisOrbit i.property) (u := fun i => T.axisRoot i.property)
      (hm := fun i => T.axisPredecessorUnit i.property)
      («φ» := φ) (η := η₀) (M := T.modulus) («e» := e) («r» := r) (H := long)
      (a := cf) (d := cb)
      (b := costF) (c := costB)
      (f := f) (g := j) (fun i : σ => T.primeAxis i.property)
      (algebraMap T.Order (JetQuotient T.modulus r)) (changeJetFintype pf) (changeJetFintype pb)
    refine changeGridFintype (aux hf hj ?_)
    intro S x y
    exact changeProductFintype (hmul S x y)
  obtain ⟨a,d,q,t,f',j',hcost,hq,ht,hmul'⟩ := grid
  have cop : Pairwise (Function.onFun Nat.Coprime (fun i : σ => i.val)) := fun i j hij =>
    (Nat.coprime_primes (T.axis_prime i.property) (T.axis_prime j.property)).2
      (fun heq => hij (Subtype.ext heq))
  have : NeZero (∏ i : σ, i.val) := ⟨(Finset.prod_pos fun i _ => hp i.val i.property).ne'⟩
  have hprod : (∏ i : σ, i.val) = ∏ p ∈ D.packing.axes, p := Finset.prod_coe_sort _ (fun p => p)
  have hvol : 8*n ≤ e*r*(∏ i : σ, i.val) := by
    rw [hprod]
    simpa only [mul_rotate] using D.packing.volume_lower
  obtain ⟨z,hz,hzCost⟩ := exists_openConvolution_of_grid φ η₀ (protectedGaussian_coordinates L).injective
    T.modulus (fun b : D.packing.DyadicPoint => T.jets (hlong b.1)) (T.packedBasis r)
    _ _ (fun i j => T.packedBasis_apply r (i,j)) (fun x z => T.jetOperandValue_eq_iff x z)
    (primeResidues (fun i : σ => i.val) cop) 1 (primeResidues_apply _ cop) he hr hvol
    q t f' j' hq ht (fun x y => changeCyclicProduct (hmul' x y))
  rw [hprod] at hzCost
  have hcost' := hcost.trans (D.packing.dyadic_transformCosts_le hn hB hp hs af ab hprime hfourier)
  convert D.packing.protectedList_of_dyadicSectors hn hB hp z hz hzCost hcost' using 2
  ring

end DyadicCoefficientTower

end FiniteFourier
end LinearAlgebra
end OAI
