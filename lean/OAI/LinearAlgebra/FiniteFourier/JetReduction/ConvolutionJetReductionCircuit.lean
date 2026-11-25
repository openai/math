import OAI.LinearAlgebra.FiniteFourier.JetReduction.ConvolutionJetReduction
import OAI.LinearAlgebra.FiniteFourier.ConvolutionJetQuadratic
import OAI.LinearAlgebra.FiniteFourier.RingFixedConvolution
import OAI.LinearAlgebra.FiniteFourier.CircuitRingCombine

/-! # Circuit size for fixed monic reduction in the jet product

The two truncated convolutions specialize integral convolution circuits at
fixed operands. Taking a half and reversing its order use only free readouts.
Each output coefficient then needs one subtraction.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace JetReduction

open Polynomial
open scoped Classical PowerSeries

noncomputable section
variable {R : Type*} [CommRing R] {e : ℕ}

private def readWires {I O : Type*} (idx : O → I) : Circuit R I O 0 :=
  ⟨.nil, fun i => .scaled 1 (.inl (idx i))⟩

private theorem readWires_eval {I O : Type*} (idx : O → I) (x : I → R) (i : O) :
    (readWires idx).eval x i = x (idx i) := by
  simp [readWires, Circuit.eval, Readout.eval]

private theorem low_coeff (p : R[X]) (i : Fin e) : (low e p).coeff i.val = p.coeff i.val := by
  simp [low, PowerSeries.coeff_trunc, i.isLt]

/-- Truncate a fixed-operand convolution to its first `e` output coefficients. -/
theorem exists_low_product_circuit {b : R[X]} (hb : b.natDegree < e) :
    ∃ s ≤ integralConvolutionCost e, ∃ q : Circuit R (Fin e) (Fin e) s,
      ∀ (a : R[X]), a.natDegree < e →
        q.eval (toFn e a) = toFn e (low e (b * a)) := by
  obtain ⟨s, hs, c, hc⟩ := exists_fixed_convolution_circuit e (toFn e b)
  let idx (i : Fin e) : Fin (2*e-1) := ⟨i.val, by have := i.isLt; omega⟩
  refine ⟨s, hs, ⟨c.program, fun i => c.output (idx i)⟩, fun a ha => ?_⟩
  funext i
  change c.eval (toFn e a) (idx i) = (low e (b * a)).coeff i.val
  rw [hc, ← ofFn_mul_coeff_openConv, ofFn_comp_toFn_eq_id_of_natDegree_lt ha,
    ofFn_comp_toFn_eq_id_of_natDegree_lt hb, low_coeff, mul_comm]

/-- A monic degree-`e` modulus reduces a length-`2e` dividend with at most two
length-`e` fixed-convolution circuits and `e` binary subtraction gates. -/
theorem exists_modByMonic_circuit (he : 0 < e) {m : R[X]} (hm : m.Monic)
    (hd : m.natDegree = e) :
    ∃ s ≤ 2 * integralConvolutionCost e + e, ∃ c : Circuit R (Fin (2*e)) (Fin e) s,
      ∀ x, c.eval x = toFn e (ofFn (2*e) x %ₘ m) := by
  let hi (i : Fin e) : Fin (2*e) := ⟨e + (e-1) - i.val, by omega⟩
  let lo (i : Fin e) : Fin (2*e) := ⟨i.val, by have := i.isLt; omega⟩
  obtain ⟨s, hs, f, hf⟩ := exists_low_product_circuit (natDegree_reciprocal_lt he m)
  let fRev : Circuit R (Fin e) (Fin e) s := ⟨f.program, fun i => f.output i.rev⟩
  obtain ⟨t, ht, q, hq⟩ := circuit_comp (readWires hi) fRev
  have hq' (p : R[X]) : q.eval (toFn (2*e) p) = toFn e (quotient e m p) := by
    have hhi : (readWires hi).eval (toFn (2*e) p) = toFn e (highRev e p) := by
      funext i
      rw [readWires_eval]
      change p.coeff (e + (e-1) - i.val) = (low e (p.reflect (e + (e-1)))).coeff i.val
      rw [low_coeff, coeff_reflect, revAt_le (by have := i.isLt; omega)]
    rw [hq, hhi]
    funext i
    change f.eval (toFn e (highRev e p)) i.rev = (quotient e m p).coeff i.val
    rw [hf (highRev e p) (natDegree_low_lt he _), quotient, coeff_reflect,
      revAt_le (by have := i.isLt; omega)]
    change Polynomial.coeff _ (e - (i.val + 1)) = Polynomial.coeff _ (e - 1 - i.val)
    congr 1
    omega
  obtain ⟨u, hu, g, hg⟩ := exists_low_product_circuit (natDegree_low_lt he m)
  obtain ⟨v, hv, correction, hc⟩ := circuit_comp q g
  obtain ⟨r, hr, c, H⟩ := circuit_sumPair _ (Fin e) (1 : R) (-1) (readWires lo) correction
  refine ⟨r, ?_, c, fun x => ?_⟩
  · simp only [Fintype.card_fin] at hr
    omega
  · let p := ofFn (2*e) x
    have hp : p.natDegree < 2*e := ofFn_natDegree_lt (by omega) x
    have hx : toFn (2*e) p = x := toFn_comp_ofFn_eq_id _ _
    rw [← reduce_eq_modByMonic he hm hd p hp]
    funext i
    rw [H, ← hx, hc, hq', hg _ (operand_degrees he m p).2.2.2, readWires_eval]
    change 1 * p.coeff i.val + (-1) * _ = (reduce e m p).coeff i.val
    rw [reduce, coeff_sub, low_coeff]
    simp [toFn, sub_eq_add_neg]

/-- For a modulus defined over the base ring, reduce the two polynomial
coordinates before combining them in the quadratic algebra. -/
theorem quadraticPolynomial_modByMonic {S : Type*} [CommRing S] (φ : R →+* S) (η : S)
    {m : R[X]} (hm : m.Monic) (u v : R[X]) :
    quadraticPolynomial φ η u v %ₘ m.map φ =
      quadraticPolynomial φ η (u %ₘ m) (v %ₘ m) := by
  simp only [quadraticPolynomial, ← smul_eq_C_mul, add_modByMonic, smul_modByMonic,
    map_modByMonic φ hm]

end
end JetReduction

end FiniteFourier
end LinearAlgebra
end OAI
