import OAI.LinearAlgebra.FiniteFourier.FixedJetCircuit

/-! # Fixed jet multipliers in operand coordinate order

Both ends of each circuit use the jet degree, coefficient degree, and quadratic
coordinate order of the mixed-radix operand. The permutation costs no gates.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S] {e h : ℕ}

/-- Interpret the coordinates of an operand in a single jet block. -/
def jetOperandValue (φ : R →+* S) (η : S) (m : S[X])
    (x : (Fin h × Fin e) × Fin 2 → R) : JetQuotient m h :=
  jetQuotientValue m (quadraticJetArray φ η (fun i => x (i,0)) (fun i => x (i,1)))

private theorem jetOperandValue_eq_output (φ : R →+* S) (η : S) (m : S[X])
    (x : (Fin h × Fin e) × Fin 2 → R) :
    jetOperandValue φ η m x = jetOutputValueOver φ η m (fun i => x ((i.1.2,i.2),i.1.1)) := by
  rw [jetOutputValueOver_eq_jetQuotientValue]
  rfl

private def operandOrder {g : ℕ}
    (p : Circuit R ((Fin 2 × Fin h) × Fin e) ((Fin 2 × Fin h) × Fin e) g) :
    Circuit R ((Fin h × Fin e) × Fin 2) ((Fin h × Fin e) × Fin 2) g :=
  p.rewire (fun i => (1,(i.1.2,i.2),i.1.1)) (fun i => (1,(i.2,i.1.1),i.1.2))

private theorem operandOrder_correct (φ : R →+* S) (η : S) (m : S[X]) (z : JetQuotient m h)
    {g : ℕ} {p : Circuit R ((Fin 2 × Fin h) × Fin e) ((Fin 2 × Fin h) × Fin e) g}
    (hp : ∀ x, jetOutputValueOver φ η m (p.eval x) = z * jetOutputValueOver φ η m x)
    (x : (Fin h × Fin e) × Fin 2 → R) :
    jetOperandValue φ η m ((operandOrder p).eval x) = z * jetOperandValue φ η m x := by
  simp only [jetOperandValue_eq_output, operandOrder, Circuit.eval_rewire, one_mul]
  exact hp _

variable {φ : R →+* S} {η : S} {m : S[X]}

/-- Multiplication by any fixed jet in operand coordinates pays for the encoder
once, the decoder once, and three fixed-operand scalar convolution circuits. -/
theorem JetCircuitsOver.operandScale (jets : JetCircuitsOver φ η m e h)
    (basis : Function.Bijective (fun u : Fin 2 → R => φ (u 0) + η * φ (u 1)))
    (hm : m.Monic) (hd : m.natDegree = e) (he : 0 < e) (z : JetQuotient m h) :
    ∃ g ≤ 2*e*h + 3*integralConvolutionCost (2*e*h) + 3*(2*(2*e*h)-1) +
        h*(6*(2*integralConvolutionCost e+e)+2*e),
      ∃ q : Circuit R ((Fin h × Fin e) × Fin 2) ((Fin h × Fin e) × Fin 2) g,
        ∀ x, jetOperandValue φ η m (q.eval x) = z * jetOperandValue φ η m x := by
  obtain ⟨g,hg,p,hp⟩ := jets.fixedMultiplier basis hm hd he z
  exact ⟨g,hg,operandOrder p,operandOrder_correct φ η m z hp⟩

/-- Under the common cutoff for the three child convolutions, each coefficient
of the rectangular array incurs at most forty times the shorter-length envelope. -/
theorem JetCircuitsOver.operandScale_envelope (jets : JetCircuitsOver φ η m e h)
    (basis : Function.Bijective (fun u : Fin 2 → R => φ (u 0) + η * φ (u 1)))
    (hm : m.Monic) (hd : m.natDegree = e) (he : 0 < e) (hh : 0 < h) {s : ℕ}
    (hc : 2*e*h ≤ s) (z : JetQuotient m h) :
    ∃ g : ℕ, (g : ℝ) ≤ 40*e*h*convolutionEnvelope s ∧
      ∃ q : Circuit R ((Fin h × Fin e) × Fin 2) ((Fin h × Fin e) × Fin 2) g,
        ∀ x, jetOperandValue φ η m (q.eval x) = z * jetOperandValue φ η m x := by
  obtain ⟨g,hg,p,hp⟩ := jets.fixedMultiplier_envelope basis hm hd he hh hc z
  exact ⟨g,hg,operandOrder p,operandOrder_correct φ η m z hp⟩

end

end FiniteFourier
end LinearAlgebra
end OAI
