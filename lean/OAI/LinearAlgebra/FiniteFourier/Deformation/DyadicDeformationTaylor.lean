import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionDeformation
import OAI.LinearAlgebra.FiniteFourier.ConvolutionJetCyclotomic
import OAI.LinearAlgebra.FiniteFourier.TaylorShiftCircuit

/-! # Coordinate circuits for the Taylor stages of jet deformation

An integer translation commutes with every additive coordinate decoder. Applying
the denominator-free Taylor circuit to each of the two scalar coordinates of
every cyclotomic coefficient implements both directions of the precision change.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial
open scoped BigOperators Classical

noncomputable section

variable {R A S κ : Type*} [CommRing R] [CommRing A] [CommRing S]

private theorem shift_integer_formula (c : ℤ) {h : ℕ} (x : Fin h → R) (k : ℕ) :
    shiftedCoefficient (c : R) x k =
      ∑ i, (c ^ (i.val-k) * (i.val.choose k : ℤ)) • x i := by
  change (taylor (c : R) (∑ i, monomial i.val (x i))).coeff k = _
  simp only [map_sum, taylor_monomial, finsetSum_coeff, coeff_C_mul, coeff_X_add_C_pow,
    zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_natCast, mul_comm (x _)]

/-- Every row of the shifted vector decodes to the corresponding coefficient over
the larger ring. Integer shifts only require additivity of the decoder. -/
theorem decode_integer_shift (δ : (κ → R) →+ A) (c : ℤ) {h : ℕ} (x : Fin h → κ → R) (k : ℕ) :
    δ (fun z => shiftedCoefficient (c : R) (fun t => x t z) k) =
      shiftedCoefficient (c : A) (fun t => δ (x t)) k := by
  let w (i : Fin h) := c ^ (i.val-k) * (i.val.choose k : ℤ)
  have hv : (fun z => shiftedCoefficient (c : R) (fun t => x t z) k) = ∑ i, w i • x i := by
    funext z
    simp only [shift_integer_formula, w, Finset.sum_apply, Pi.smul_apply]
  rw [hv, shift_integer_formula, map_sum]
  simp only [map_zsmul, w]

/-- The scalar coefficients in a single cyclotomic row decode additively. -/
def jetRowDecoder (φ : R →+* S) (η : S) (m : S[X]) (e : ℕ) :
    (Fin 2 × Fin e → R) →+ AdjoinRoot m where
  toFun x := AdjoinRoot.mk m (ofFn e fun i => φ (x (0,i)) + η * φ (x (1,i)))
  map_zero' := by
    simp only [Pi.zero_apply, map_zero, mul_zero, add_zero]
    rw [show (fun _ : Fin e => (0:S)) = 0 from rfl, map_zero, map_zero]
  map_add' x y := by
    rw [← map_add, ← map_add]
    congr 2
    funext i
    simp only [Pi.add_apply, map_add, mul_add]
    abel

private theorem jetOutputValueOver_eq_rows (φ : R →+* S) (η : S) (m : S[X]) {e h : ℕ}
    (x : (Fin 2 × Fin h) × Fin e → R) :
    jetOutputValueOver φ η m x = AdjoinRoot.mk (X ^ h) (vectorPolynomial (fun t =>
      jetRowDecoder φ η m e (fun i => x ((i.1,t),i.2)))) := by
  simp only [jetOutputValueOver, ofFn_eq_sum_monomial, jetRowDecoder, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, vectorPolynomial, Polynomial.map_sum, map_monomial]

private theorem specialize_as_mk (a : R) (h : ℕ) (p : R[X]) :
    specialize a h p = AdjoinRoot.mk (X ^ h) (taylor a p) := AdjoinRoot.aeval_eq ..

private theorem liftJet_vector (a : R) (h : ℕ) (x : Fin h → R) :
    liftJet a h (AdjoinRoot.mk (X ^ h) (vectorPolynomial x)) = taylor (-a) (vectorPolynomial x) := by
  nontriviality R
  change taylor (-a) (AdjoinRoot.modByMonicHom _ (AdjoinRoot.mk _ _)) = _
  rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff (monic_X_pow h)).mpr]
  rw [vectorPolynomial_eq_ofFn, degree_X_pow]
  exact ofFn_degree_lt x

/-- Forming the represented polynomial after shifting, with truncation or zero padding
to a new length, computes the change of jet center and precision. -/
theorem jetValue_shift (n N : ℕ) (a b : R) (x : Fin n → R) :
    AdjoinRoot.mk (X ^ N)
        (vectorPolynomial (fun j : Fin N => shiftedCoefficient (b-a) x j.val)) =
      specialize b N (liftJet a n (AdjoinRoot.mk (X ^ n) (vectorPolynomial x))) := by
  rw [liftJet_vector, specialize_as_mk, taylor_taylor, ← sub_eq_add_neg,
    AdjoinRoot.mk_eq_mk, X_pow_dvd_iff]
  intro k hk
  rw [coeff_sub, vectorPolynomial_eq_ofFn, ofFn_coeff_eq_val_of_lt _ hk]
  exact sub_self _

/-- Translate every base coordinate by the specialized integer shift and use free
readouts to pad or truncate to the target precision. -/
theorem exists_jet_center_circuit (φ : R →+* S) (η : S) (m : S[X]) (e n N : ℕ)
    (hn : 0 < n) {cutoff : ℕ} (hc : 2*n ≤ cutoff) (a b : ℤ) :
    ∃ (t : ℕ) (p : Circuit R ((Fin 2 × Fin n) × Fin e) ((Fin 2 × Fin N) × Fin e) t),
      (t : ℝ) ≤ 8*e*n*(1+Real.logb 2 n)*convolutionEnvelope cutoff ∧
      ∀ x, jetOutputValueOver φ η m (p.eval x) =
        specialize (b : AdjoinRoot m) N (liftJet (a : AdjoinRoot m) n (jetOutputValueOver φ η m x)) := by
  let c := b-a
  obtain ⟨s, shift, hs, hshift⟩ := exists_taylor_shift_envelope (R := R) (e := e) hn hc (c : R)
  obtain ⟨t, ht, both, hboth⟩ := circuit_rows (Fin 2) shift
  let q := both.rewire (fun i => (1, ((i.1,i.2.1),i.2.2)))
    (fun o : (Fin 2 × Fin n) × Fin e => (1, (o.1.1, o.1.2, o.2)))
  let p : Circuit R ((Fin 2 × Fin n) × Fin e) ((Fin 2 × Fin N) × Fin e) t :=
    ⟨q.program, fun o => if h : o.1.2.val < n then q.output ((o.1.1,⟨o.1.2.val,h⟩),o.2)
      else .zero⟩
  have hval (x : (Fin 2 × Fin n) × Fin e → R) (l : Fin 2) (j : Fin N) (i : Fin e) :
      p.eval x ((l,j),i) = shiftedCoefficient (c : R) (fun t => x ((l,t),i)) j.val := by
    by_cases hj : j.val < n
    · change (if h : j.val < n then q.output ((l,⟨j.val,h⟩),i) else .zero).eval _ = _
      rw [dite_eq_left hj]
      change q.eval x ((l,⟨j.val,hj⟩),i) = _
      simp [q, Circuit.eval_rewire, hboth, hshift]
    · change (if h : j.val < n then q.output ((l,⟨j.val,h⟩),i) else .zero).eval _ = _
      rw [dite_eq_right hj]
      exact (shiftedCoefficient_eq_zero_of_ge _ _ (by omega)).symm
  refine ⟨t,p,?_,fun x => ?_⟩
  · have ht' : (t:ℝ) ≤ 2*s := by exact_mod_cast (show t ≤ 2*s by simpa using ht)
    linarith
  · let δ := jetRowDecoder φ η m e
    let rows (t : Fin n) (i : Fin 2 × Fin e) := x ((i.1,t),i.2)
    simp only [jetOutputValueOver_eq_rows, hval]
    have hj (j : Fin N) :
        δ (fun z => shiftedCoefficient (c : R) (fun t => rows t z) j.val) =
          shiftedCoefficient ((b : AdjoinRoot m)-a) (fun t => δ (rows t)) j.val := by
      simpa only [c, Int.cast_sub] using decode_integer_shift δ c rows j.val
    exact (congrArg (fun f : Fin N → AdjoinRoot m => AdjoinRoot.mk _ (vectorPolynomial f))
      (funext hj)).trans (jetValue_shift n N _ _ _)

/-- The short-to-long input Taylor circuit used by both protected covers. -/
theorem exists_jet_input_shift_circuit (φ : R →+* S) (η : S) (m : S[X]) (e r H : ℕ)
    (hr : 0 < r) {cutoff : ℕ} (hc : 2*r ≤ cutoff) :
    ∃ (t : ℕ) (p : Circuit R ((Fin 2 × Fin r) × Fin e) ((Fin 2 × Fin H) × Fin e) t),
      (t : ℝ) ≤ 8*e*r*(1+Real.logb 2 r)*convolutionEnvelope cutoff ∧
      ∀ x, jetOutputValueOver φ η m (p.eval x) =
        specialize 0 H (liftJet 1 r (jetOutputValueOver φ η m x)) := by
  simpa only [Int.cast_one, Int.cast_zero] using exists_jet_center_circuit φ η m e r H hr hc 1 0

/-- The long-to-short Taylor circuit recovers the endpoint at one. -/
theorem exists_jet_output_shift_circuit (φ : R →+* S) (η : S) (m : S[X]) (e H r : ℕ)
    (hH : 0 < H) {cutoff : ℕ} (hc : 2*H ≤ cutoff) :
    ∃ (t : ℕ) (p : Circuit R ((Fin 2 × Fin H) × Fin e) ((Fin 2 × Fin r) × Fin e) t),
      (t : ℝ) ≤ 8*e*H*(1+Real.logb 2 H)*convolutionEnvelope cutoff ∧
      ∀ x, jetOutputValueOver φ η m (p.eval x) =
        readAtOne H r (jetOutputValueOver φ η m x) := by
  simpa only [readAtOne, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Int.cast_one,
    Int.cast_zero] using exists_jet_center_circuit φ η m e H r hH hc 0 1

end

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
