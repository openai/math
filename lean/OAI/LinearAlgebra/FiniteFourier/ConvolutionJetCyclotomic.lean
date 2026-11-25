import OAI.LinearAlgebra.FiniteFourier.ConvolutionJetCircuit
import OAI.LinearAlgebra.FiniteFourier.ConvolutionJetCircuitDescent
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-! # Cyclotomic jet multiplication over the Gaussian and Eisenstein orders

The fixed modulus for each row is the image of the integral cyclotomic
polynomial `Φ_M`. Its degree is `φ(M)` over every nontrivial base ring.
The first quadratic extension is obtained by adjoining a zero of `Φ₄`
or `Φ₃`, with power basis `1, η`.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

section

open Polynomial

variable (R : Type*) [CommRing R]

private theorem cyclotomic_four_eq : cyclotomic 4 R = X ^ 2 + 1 := by
  have H := cyclotomic_prime_pow_eq_geom_sum (R := R) (n := 1) Nat.prime_two
  simpa [Finset.sum_range_succ, add_comm] using H

/-- The Gaussian generator satisfies `η² = -1`. -/
theorem gaussian_root_relation :
    let S := AdjoinRoot (cyclotomic 4 R)
    let η := AdjoinRoot.root (cyclotomic 4 R)
    η^2 = algebraMap R S (-1) + η * algebraMap R S 0 := by
  dsimp only
  simp only [map_neg, map_one, map_zero, mul_zero, add_zero]
  apply eq_neg_of_add_eq_zero_left
  simpa only [cyclotomic_four_eq, eval₂_add, eval₂_pow, eval₂_X, eval₂_one] using
    AdjoinRoot.eval₂_root (cyclotomic 4 R)

/-- The Eisenstein generator satisfies `η² = -1 - η`. -/
theorem eisenstein_root_relation :
    let S := AdjoinRoot (cyclotomic 3 R)
    let η := AdjoinRoot.root (cyclotomic 3 R)
    η^2 = algebraMap R S (-1) + η * algebraMap R S (-1) := by
  dsimp only
  simp only [map_neg, map_one, mul_neg, mul_one]
  have H := AdjoinRoot.eval₂_root (cyclotomic 3 R)
  rw [cyclotomic_three] at H ⊢
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at H
  linear_combination H

/-- Three length-`2 φ(M) h` base-ring convolutions multiplied by fixed linear
encoder and decoder circuits compute a product in
`(R[η][Y]/(Φ_M))[z]/(z^h)`, for `η` a root of `Φ_k`. -/
def CyclotomicJetCircuits (k M h : ℕ) : Prop :=
  let e := M.totient
  let m := cyclotomic M R
  let φ := algebraMap R (AdjoinRoot (cyclotomic k R))
  let η := AdjoinRoot.root (cyclotomic k R)
  ∃ (u v : ℕ) (enc : Circuit R ((Fin h × Fin e) × Fin 2) (Σ _ : Fin (2*e*h), Fin 3) u)
    (dec : Circuit R (Σ _ : Fin (2*(2*e*h)-1), Fin 3) ((Fin 2 × Fin h) × Fin e) v),
    u ≤ 2*e*h ∧ v ≤ 3*(2*(2*e*h)-1) + 2*h*(2*integralConvolutionCost e+e) ∧
    ∀ x y, let z := fun k : Σ _ : Fin (2*(2*e*h)-1), Fin 3 =>
      openConv R (2*e*h) (fun i => enc.eval x ⟨i,k.2⟩) (fun i => enc.eval y ⟨i,k.2⟩) k.1
    jetOutputValue φ η m (dec.eval z) =
      jetQuotientValue (m.map φ) (quadraticJetArray φ η (fun i => x (i,0)) (fun i => x (i,1))) *
      jetQuotientValue (m.map φ) (quadraticJetArray φ η (fun i => y (i,0)) (fun i => y (i,1)))

variable [Nontrivial R] {M h : ℕ}

/-- The fixed three-child reduction for cyclotomic jets over the Gaussian order. -/
theorem gaussian_cyclotomicJet_circuits (hM : 0 < M) (hh : 0 < h) :
    CyclotomicJetCircuits R 4 M h :=
  exists_jetProduct_circuits _ _ (-1 : R) 0 (gaussian_root_relation R)
    (Nat.totient_pos.mpr hM) hh (cyclotomic.monic M R) (natDegree_cyclotomic M R)

/-- The fixed three-child reduction for cyclotomic jets over the Eisenstein order. -/
theorem eisenstein_cyclotomicJet_circuits (hM : 0 < M) (hh : 0 < h) :
    CyclotomicJetCircuits R 3 M h :=
  exists_jetProduct_circuits _ _ (-1 : R) (-1) (eisenstein_root_relation R)
    (Nat.totient_pos.mpr hM) hh (cyclotomic.monic M R) (natDegree_cyclotomic M R)

end

section

open Polynomial
open scoped Classical

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S] {e h : ℕ}

/-- Interpret the decoded coefficient array with a modulus over the quadratic order. -/
def jetOutputValueOver (φ : R →+* S) (η : S) (m : S[X]) (y : (Fin 2 × Fin h) × Fin e → R) :
    JetQuotient m h :=
  AdjoinRoot.mk (X ^ h) ((ofFn h fun t => ofFn e fun i =>
    φ (y ((0,t),i)) + η * φ (y ((1,t),i))).map (AdjoinRoot.mk m))

/-- Product circuits with an arbitrary coefficient modulus over the quadratic order.
The fixed monic-reduction circuit in each row is restricted to the two base
coordinates before independent copies are run. -/
def JetCircuitsOver (φ : R →+* S) (η : S) (m : S[X]) (e h : ℕ) : Prop :=
  ∃ (u v : ℕ) (enc : Circuit R ((Fin h × Fin e) × Fin 2) (Σ _ : Fin (2*e*h), Fin 3) u)
    (dec : Circuit R (Σ _ : Fin (2*(2*e*h)-1), Fin 3) ((Fin 2 × Fin h) × Fin e) v),
    u ≤ 2*e*h ∧ v ≤ 3*(2*(2*e*h)-1) + h*(6*(2*integralConvolutionCost e+e) + 2*e) ∧
    ∀ x y, let z := fun k : Σ _ : Fin (2*(2*e*h)-1), Fin 3 =>
      openConv R (2*e*h) (fun i => enc.eval x ⟨i,k.2⟩) (fun i => enc.eval y ⟨i,k.2⟩) k.1
    jetOutputValueOver φ η m (dec.eval z) =
      jetQuotientValue m (quadraticJetArray φ η (fun i => x (i,0)) (fun i => x (i,1))) *
      jetQuotientValue m (quadraticJetArray φ η (fun i => y (i,0)) (fun i => y (i,1)))

theorem exists_jetProduct_circuits_over (φ : R →+* S) (η : S) (c d : R)
    (hη : η^2 = φ c + η*φ d) (span : ∀ s, ∃ a b : R, φ a + η*φ b = s)
    (he : 0 < e) (hh : 0 < h) {m : S[X]} (hm : m.Monic) (hd : m.natDegree = e) :
    JetCircuitsOver φ η m e h := by
  classical
  obtain ⟨u, hu, enc, henc⟩ := exists_jetChildInput_circuit R e h
  obtain ⟨_, v, _, dec, _, hv, _, hdec⟩ := exists_quadratic_convolution_circuits c d (2*e*h)
  obtain ⟨v₁,hv₁,red,hred⟩ := JetReduction.exists_modByMonic_circuit he hm hd
  obtain ⟨v₂,hv₂,restrict,hrestrict⟩ := QuadraticDescent.circuit φ η hη span red
  obtain ⟨v₃,hv₃,rows,hrows⟩ := circuit_rows (Fin h) restrict
  let pack : Circuit R (Σ _ : Fin (2*(2*e*h)-1), Fin 2) (Fin h × (Fin (2*e) × Fin 2)) 0 :=
    ⟨.nil, fun i => match jetRowSource e h i.1 i.2.1 with
      | some k => .scaled 1 (.inl ⟨k,i.2.2⟩)
      | none => .zero⟩
  obtain ⟨v₄,hv₄,pre,hpre⟩ := circuit_comp dec pack
  obtain ⟨v₅,hv₅,out,hout⟩ := circuit_comp pre rows
  let result : Circuit R _ ((Fin 2 × Fin h) × Fin e) v₅ :=
    ⟨out.program, fun i => out.output (i.1.2,(i.2,i.1.1))⟩
  refine ⟨u,v₅,enc,result,hu,?_,?_⟩
  · simp only [Fintype.card_fin] at hv₂ hv₃
    have H := Nat.mul_le_mul_left h (show v₂ ≤ 6*(2*integralConvolutionCost e+e)+2*e by omega)
    omega
  · intro x y
    dsimp only
    let z := fun k : Σ _ : Fin (2*(2*e*h)-1), Fin 3 =>
      openConv R (2*e*h) (fun i => enc.eval x ⟨i,k.2⟩) (fun i => enc.eval y ⟨i,k.2⟩) k.1
    let zS := fun k : Fin (2*(2*e*h)-1) =>
      φ (jetDecodeCoordinate c d z 0 k) + η * φ (jetDecodeCoordinate c d z 1 k)
    have Hpre (t : Fin h) :
        QuadraticDescent.decode φ η (fun j => pre.eval z (t,j)) = jetScalarRow zS t := by
      funext j
      simp only [QuadraticDescent.decode, hpre]
      cases H : jetRowSource e h t j with
      | none => simp [pack, Circuit.eval, H, jetScalarRow, Readout.eval]
      | some k =>
        change φ ((pack.eval (dec.eval z)) (t,j,0)) + η * φ ((pack.eval (dec.eval z)) (t,j,1)) = _
        have hpack (i : Fin 2) : pack.eval (dec.eval z) (t,j,i) = dec.eval z ⟨k,i⟩ := by
          simp [pack, Circuit.eval, Readout.eval, H]
        simp only [hpack, hdec, jetScalarRow, H, zS, jetDecodeCoordinate]
    have Hrow (t : Fin h) (i : Fin e) :
        φ (result.eval z ((0,t),i)) + η * φ (result.eval z ((1,t),i)) =
          (ofFn (2*e) (jetScalarRow zS t) %ₘ m).coeff i := by
      change φ (out.eval z (t,i,0)) + η * φ (out.eval z (t,i,1)) = _
      simp only [hout, hrows]
      change QuadraticDescent.decode φ η (restrict.eval (fun j => pre.eval z (t,j))) i = _
      rw [hrestrict, Hpre, hred]
      rfl
    have Hz : ofFn _ zS = jetChildProduct φ η c d (fun i => x (i,0)) (fun i => x (i,1))
        (fun i => y (i,0)) (fun i => y (i,1)) := by
      unfold jetChildProduct
      apply congrArg
      funext k
      simp [zS, jetDecodeCoordinate, z, henc]
    change jetOutputValueOver φ η m (result.eval z) = _
    calc
      _ = AdjoinRoot.mk (X ^ h) ((jetProductRows e h m (ofFn _ zS)).map (AdjoinRoot.mk m)) := by
        rcases subsingleton_or_nontrivial S with hS | hS
        · have hm0 : m = 0 := Subsingleton.elim _ _
          simp [hm0] at hd
          omega
        have hm1 : m ≠ 1 := by rintro rfl; simp at hd; omega
        unfold jetOutputValueOver jetProductRows
        congr 2
        congr 1
        funext t
        simp only [Hrow, ← ofFn_jetScalarRow]
        exact ofFn_comp_toFn_eq_id_of_natDegree_lt ((natDegree_modByMonic_lt _ hm hm1).trans_eq hd)
      _ = _ := by rw [Hz, jetChildProduct_eq φ η c d hη he hh]; exact jetProductRows_correct m hm _ _

/-- The Gaussian power basis spans over the base ring. -/
theorem gaussianSpan (R : Type*) [CommRing R] [Nontrivial R]
    (s : AdjoinRoot (cyclotomic 4 R)) :
    ∃ a b : R, algebraMap R _ a + AdjoinRoot.root (cyclotomic 4 R) * algebraMap R _ b = s := by
  let m := cyclotomic 4 R
  let hm : m.Monic := cyclotomic.monic 4 R
  let p := AdjoinRoot.modByMonicHom hm s
  have hd : m.natDegree = 2 := by rw [show m = cyclotomic 4 R from rfl, natDegree_cyclotomic]; decide
  have hm1 : m ≠ 1 := by intro h; simp [h] at hd
  have hdeg : p.natDegree < 2 := by
    obtain ⟨u, rfl⟩ := AdjoinRoot.mk_surjective s
    exact (natDegree_modByMonic_lt u hm hm1).trans_eq hd
  have hp : p = C (p.coeff 0) + C (p.coeff 1)*X := by
    calc
      p = ofFn 2 (toFn 2 p) := (ofFn_comp_toFn_eq_id_of_natDegree_lt hdeg).symm
      _ = _ := by simp [ofFn_eq_sum_monomial, Fin.sum_univ_two, toFn, ← C_mul_X_pow_eq_monomial]
  refine ⟨p.coeff 0, p.coeff 1, ?_⟩
  have hp' := congrArg (AdjoinRoot.mk m) hp
  rw [show AdjoinRoot.mk m p = s from AdjoinRoot.mk_leftInverse hm s, map_add, map_mul] at hp'
  exact (by simpa [AdjoinRoot.mk_C, AdjoinRoot.mk_X, mul_comm, AdjoinRoot.algebraMap_eq] using hp'.symm)

/-- Multiplication in jets over a monic modulus with arbitrary Gaussian coefficients. -/
theorem gaussian_jet_circuits_over (R : Type*) [CommRing R] [Nontrivial R] {e h : ℕ}
    (he : 0 < e) (hh : 0 < h) (m : (AdjoinRoot (cyclotomic 4 R))[X])
    (hm : m.Monic) (hd : m.natDegree = e) :
    JetCircuitsOver (algebraMap R _) (AdjoinRoot.root (cyclotomic 4 R)) m e h :=
  exists_jetProduct_circuits_over _ _ (-1 : R) 0 (gaussian_root_relation R)
    (gaussianSpan R) he hh hm hd

end

end

end FiniteFourier
end LinearAlgebra
end OAI
