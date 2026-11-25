import OAI.LinearAlgebra.FiniteFourier.ConvolutionJet
import OAI.LinearAlgebra.FiniteFourier.JetReduction.ConvolutionJetReductionCircuit

/-! # Reading the reduced rows of a packed jet product

Each row has `2e-1` packed coefficients. Append a zero coefficient before
running the two length-`2e` monic-reduction inputs for its quadratic
coordinates.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial
open scoped Classical
noncomputable section

private theorem jetRowIndex_lt {e h k : ℕ} (t : Fin h) (hk : k < 2*e-1) :
    t.val * (2*e-1) + k < 2*(2*e*h)-1 := by
  have ht := Nat.mul_le_mul_right (2*e-1) t.isLt
  change (t.val+1)*(2*e-1) ≤ h*(2*e-1) at ht
  rw [Nat.add_mul, one_mul] at ht
  have hd : h*(2*e-1) ≤ 2*e*h :=
    (Nat.mul_le_mul_left h (Nat.sub_le (2*e) 1)).trans_eq (Nat.mul_comm _ _)
  omega

/-- Read the packed coefficient in a jet row. The last slot is zero padding. -/
def jetRowSource (e h : ℕ) (t : Fin h) (i : Fin (2*e)) :
    Option (Fin (2*(2*e*h)-1)) :=
  if hi : i.val < 2*e-1 then some ⟨t.val * (2*e-1) + i.val, jetRowIndex_lt t hi⟩ else none

variable {R S : Type*} [CommRing R] [CommRing S] {e h : ℕ}

/-- The padded input vector for reducing a single scalar coordinate of a row. -/
def jetScalarRow (p : Fin (2*(2*e*h)-1) → R) (t : Fin h) (i : Fin (2*e)) : R :=
  match jetRowSource e h t i with
  | some j => p j
  | none => 0

theorem ofFn_jetScalarRow (p : Fin (2*(2*e*h)-1) → R) (t : Fin h) :
    ofFn (2*e) (jetScalarRow p t) = unpackJetRow e (ofFn _ p) t.val := by
  ext k
  by_cases hk : k < 2*e-1
  · have hk' : k < 2*e := by omega
    rw [ofFn_coeff_eq_val_of_lt _ hk', unpackJetRow, ofFn_coeff_eq_val_of_lt _ hk]
    simp only [jetScalarRow, jetRowSource, hk, dite_true]
    exact (ofFn_coeff_eq_val_of_lt p (jetRowIndex_lt t hk)).symm
  · rw [unpackJetRow, ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)]
    by_cases hk' : k < 2*e
    · rw [ofFn_coeff_eq_val_of_lt _ hk']
      simp [jetScalarRow, jetRowSource, hk]
    · exact ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk')

private theorem unpackJetRow_quadratic (φ : R →+* S) (η : S) (u v : R[X]) (t : ℕ) :
    unpackJetRow e (quadraticPolynomial φ η u v) t =
      quadraticPolynomial φ η (unpackJetRow e u t) (unpackJetRow e v t) := by
  ext k
  rw [quadraticPolynomial_coeff]
  unfold unpackJetRow
  by_cases hk : k < 2*e-1
  · simp [hk, quadraticPolynomial_coeff]
  · simp [ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)]

/-- Reducing both base-ring coordinates and decoding them gives the row of
the quadratic product reduced by the scalar extension of the modulus. -/
theorem jetReducedRow_decode (φ : R →+* S) (η : S) {m : R[X]} (hm : m.Monic)
    (p₀ p₁ : Fin (2*(2*e*h)-1) → R) (t : Fin h) :
    quadraticPolynomial φ η (ofFn (2*e) (jetScalarRow p₀ t) %ₘ m)
      (ofFn (2*e) (jetScalarRow p₁ t) %ₘ m) =
    unpackJetRow e (quadraticPolynomial φ η (ofFn _ p₀) (ofFn _ p₁)) t.val %ₘ m.map φ := by
  rw [ofFn_jetScalarRow, ofFn_jetScalarRow, unpackJetRow_quadratic,
    JetReduction.quadraticPolynomial_modByMonic φ η hm]

end

end FiniteFourier
end LinearAlgebra
end OAI
