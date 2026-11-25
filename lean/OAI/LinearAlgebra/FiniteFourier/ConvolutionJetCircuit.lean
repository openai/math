import OAI.LinearAlgebra.FiniteFourier.ConvolutionJetPackingCircuit
import OAI.LinearAlgebra.FiniteFourier.ConvolutionJetParallel
import OAI.LinearAlgebra.FiniteFourier.ConvolutionJetReadout

/-! # Three open convolutions for multiplication in a cyclotomic jet ring

The common input circuit packs the two quadratic coordinates. The output
circuit decodes their base-ring product, reads the first jet rows, and reduces
each coordinate row by a fixed monic modulus. All linear gate coefficients
belong to the base ring.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial
open scoped Classical

noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S] {e h : ℕ}

/-- Each base-coordinate wire of the Karatsuba decoder. -/
def jetDecodeCoordinate (c d : R) {n : ℕ} (p : (Σ _ : Fin n, Fin 3) → R)
    (q : Fin 2) (k : Fin n) : R :=
  let y := quadraticDecode c d (fun j => p ⟨k, j⟩)
  if q = 0 then y.1 else y.2

/-- The readout expected of the output circuit, indexed by quadratic
coordinate, jet degree and cyclotomic degree. -/
def jetOutputCoordinate (m : R[X]) (c d : R) (p : (Σ _ : Fin (2*(2*e*h)-1), Fin 3) → R)
    (i : (Fin 2 × Fin h) × Fin e) : R :=
  (ofFn (2*e) (jetScalarRow (jetDecodeCoordinate c d p i.1.1) i.1.2) %ₘ m).coeff i.2.val

private def paddedRowCircuit (R : Type*) [CommRing R] (e h : ℕ) :
    Circuit R (Σ _ : Fin (2*(2*e*h)-1), Fin 2) ((Fin 2 × Fin h) × Fin (2*e)) 0 where
  program := .nil
  output i := match jetRowSource e h i.1.2 i.2 with
    | some k => .scaled 1 (.inl ⟨k,i.1.1⟩)
    | none => .zero

private theorem paddedRowCircuit_eval (x : (Σ _ : Fin (2*(2*e*h)-1), Fin 2) → R)
    (q : Fin 2) (t : Fin h) (i : Fin (2*e)) :
    (paddedRowCircuit R e h).eval x ((q,t),i) = jetScalarRow (fun k => x ⟨k,q⟩) t i := by
  cases hk : jetRowSource e h t i <;>
    simp [paddedRowCircuit, Circuit.eval, Readout.eval, jetScalarRow, hk]

/-- The output circuit uses three linear recombination gates at every packed
output and two fixed length-`e` convolutions per base coordinate per row. -/
theorem exists_jetOutput_circuit (c d : R) {m : R[X]} (he : 0 < e)
    (hm : m.Monic) (hd : m.natDegree = e) (h : ℕ) :
    ∃ v ≤ 3*(2*(2*e*h)-1) + 2*h*(2*integralConvolutionCost e+e),
      ∃ dec : Circuit R (Σ _ : Fin (2*(2*e*h)-1), Fin 3) ((Fin 2 × Fin h) × Fin e) v,
        ∀ p i, dec.eval p i = jetOutputCoordinate m c d p i := by
  obtain ⟨_, u, _, decode, _, hu, _, hu'⟩ := exists_quadratic_convolution_circuits c d (2*e*h)
  obtain ⟨v, hv, reduce, hv'⟩ := JetReduction.exists_modByMonic_circuit he hm hd
  obtain ⟨w, hw, rows, hw'⟩ := circuit_quadratic_rows h reduce
  obtain ⟨s, hs, raw, hs'⟩ := circuit_comp decode (paddedRowCircuit R e h)
  obtain ⟨z, hz, out, hout⟩ := circuit_comp raw rows
  refine ⟨z, ?_, out, ?_⟩
  · have := Nat.mul_le_mul_left (2*h) hv
    omega
  · intro p ⟨⟨q,t⟩,i⟩
    rw [hout, hw']
    have H : (fun j => raw.eval p ((q,t),j)) = jetScalarRow (jetDecodeCoordinate c d p q) t := by
      funext j
      rw [hs', paddedRowCircuit_eval]
      congr 1
      funext k
      exact hu' p k q
    rw [H, hv']
    rfl

/-- Interpret a vector of output coordinates in the actual iterated quotient. -/
def jetOutputValue (φ : R →+* S) (η : S) (m : R[X]) (y : (Fin 2 × Fin h) × Fin e → R) :
    JetQuotient (m.map φ) h :=
  AdjoinRoot.mk (X ^ h) ((ofFn h fun t =>
    quadraticPolynomial φ η (ofFn e (fun i => y ((0,t),i))) (ofFn e (fun i => y ((1,t),i)))).map
    (AdjoinRoot.mk (m.map φ)))

private theorem quadraticPolynomial_ofFn (φ : R →+* S) (η : S) {n : ℕ} (u v : Fin n → R) :
    quadraticPolynomial φ η (ofFn n u) (ofFn n v) = ofFn n (fun i => φ (u i) + η * φ (v i)) := by
  ext k
  rw [quadraticPolynomial_coeff]
  by_cases hk : k < n
  · simp only [ofFn_coeff_eq_val_of_lt _ hk]
  · simp only [ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk), map_zero, mul_zero, add_zero]

/-- Reading and reducing both decoded coordinates computes their reduction in
the quadratic coefficient order. -/
theorem jetOutputCoordinate_value (φ : R →+* S) (η : S) {m : R[X]} (c d : R) (he : 0 < e)
    (hm : m.Monic) (hd : m.natDegree = e) (p : (Σ _ : Fin (2*(2*e*h)-1), Fin 3) → R) :
    jetOutputValue φ η m (jetOutputCoordinate m c d p) = AdjoinRoot.mk (X ^ h)
      ((jetProductRows e h (m.map φ)
        (quadraticPolynomial φ η (ofFn _ (jetDecodeCoordinate c d p 0))
          (ofFn _ (jetDecodeCoordinate c d p 1)))).map (AdjoinRoot.mk (m.map φ))) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have hz : m = 0 := Subsingleton.elim _ _
    simp [hz] at hd
    omega
  have hm1 : m ≠ 1 := by rintro rfl; simp at hd; omega
  unfold jetOutputValue jetProductRows
  apply congrArg (fun f : Polynomial S[X] => AdjoinRoot.mk ((X : (AdjoinRoot (m.map φ))[X]) ^ h)
    (f.map (AdjoinRoot.mk (m.map φ))))
  apply congrArg (ofFn h)
  funext t
  let row (q : Fin 2) := ofFn (2*e) (jetScalarRow (jetDecodeCoordinate c d p q) t)
  have H (q : Fin 2) : ofFn e (fun i => jetOutputCoordinate m c d p ((q,t),i)) = row q %ₘ m :=
    ofFn_comp_toFn_eq_id_of_natDegree_lt (p := row q %ₘ m)
      ((natDegree_modByMonic_lt (row q) hm hm1).trans_eq hd)
  rw [H, H]
  exact jetReducedRow_decode φ η hm _ _ t

/-- One list of three convolution gates, with the same encoder applied to each
operand, suffices for multiplication over a monic base-defined coefficient
modulus. The bounds count binary gates in the two surrounding linear circuits. -/
theorem exists_jetProduct_circuits (φ : R →+* S) (η : S) (c d : R)
    (hη : η^2 = φ c + η*φ d) (he : 0 < e) (hh : 0 < h) {m : R[X]}
    (hm : m.Monic) (hd : m.natDegree = e) :
    ∃ (u v : ℕ) (enc : Circuit R ((Fin h × Fin e) × Fin 2) (Σ _ : Fin (2*e*h), Fin 3) u)
      (dec : Circuit R (Σ _ : Fin (2*(2*e*h)-1), Fin 3) ((Fin 2 × Fin h) × Fin e) v),
      u ≤ 2*e*h ∧ v ≤ 3*(2*(2*e*h)-1) + 2*h*(2*integralConvolutionCost e+e) ∧
      ∀ x y, let z := fun k : Σ _ : Fin (2*(2*e*h)-1), Fin 3 =>
        openConv R (2*e*h) (fun i => enc.eval x ⟨i,k.2⟩) (fun i => enc.eval y ⟨i,k.2⟩) k.1
      jetOutputValue φ η m (dec.eval z) =
        jetQuotientValue (m.map φ) (quadraticJetArray φ η (fun i => x (i,0)) (fun i => x (i,1))) *
        jetQuotientValue (m.map φ) (quadraticJetArray φ η (fun i => y (i,0)) (fun i => y (i,1))) := by
  obtain ⟨u, hu, enc, henc⟩ := exists_jetChildInput_circuit R e h
  obtain ⟨v, hv, dec, hdec⟩ := exists_jetOutput_circuit c d he hm hd h
  refine ⟨u, v, enc, dec, hu, hv, fun x y => ?_⟩
  dsimp only
  simp_rw [henc]
  let p := fun k : Σ _ : Fin (2*(2*e*h)-1), Fin 3 =>
    openConv R (2*e*h) (jetChildInput (fun i => x (i,0)) (fun i => x (i,1)) k.2)
      (jetChildInput (fun i => y (i,0)) (fun i => y (i,1)) k.2) k.1
  change jetOutputValue φ η m (dec.eval p) = _
  rw [show dec.eval p = jetOutputCoordinate m c d p from funext (hdec p),
    jetOutputCoordinate_value φ η c d he hm hd, quadraticPolynomial_ofFn]
  change AdjoinRoot.mk _ ((jetProductRows e h _ (jetChildProduct φ η c d _ _ _ _)).map _) = _
  rw [jetChildProduct_eq φ η c d hη he hh]
  exact jetProductRows_correct _ (hm.map φ) _ _

end

end FiniteFourier
end LinearAlgebra
end OAI
