import OAI.LinearAlgebra.FiniteFourier.ConvolutionJetCyclotomic

/-! # Assembling the open convolutions for a family of jet products

A common circuit extracts the quadratic coordinates of the jets from each operand.
A return circuit recovers the ordinary product from the coordinates of the block
products. Between these circuits each block has precisely three open convolutions.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial
open scoped BigOperators

variable {R S B : Type*} [CommRing R] [CommRing S] [Fintype B]
variable {n : ℕ} {e h : B → ℕ}

/-- Input coordinates of the quadratic, cyclotomic, and jet power bases. -/
abbrev JetBlockInput (e h : B → ℕ) := Σ b, (Fin (h b) × Fin (e b)) × Fin 2

/-- Recovered block-product coordinates, in the order supplied by the jet decoder. -/
abbrev JetBlockOutput (e h : B → ℕ) := Σ b, (Fin 2 × Fin (h b)) × Fin (e b)

/-- The length of each of the three ordinary convolutions in a jet block. -/
def jetBlockLength (e h : B → ℕ) (j : B × Fin 3) : ℕ := 2 * e j.1 * h j.1

/-- Value of one jet in the output of the common operand circuit. -/
noncomputable def jetBlockValue (φ : R →+* S) (η : S) (m : B → S[X])
    (x : JetBlockInput e h → R) (b : B) : JetQuotient (m b) (h b) :=
  jetQuotientValue (m b) (quadraticJetArray φ η
    (fun i => x ⟨b, i, 0⟩) (fun i => x ⟨b, i, 1⟩))

/-- The return circuit recovers every ordinary convolution coefficient whenever
the supplied coordinates represent the products of the extracted jets. -/
def RecoversFromJetProducts (φ : R →+* S) (η : S) (m : B → S[X]) {a d : ℕ}
    (extract : Circuit R (Fin n) (JetBlockInput e h) a)
    (recover : Circuit R (JetBlockOutput e h) (Fin (2*n-1)) d) : Prop :=
  ∀ (x y : Fin n → R) (z : JetBlockOutput e h → R),
    (∀ b, jetOutputValueOver φ η (m b) (fun t => z ⟨b,t⟩) =
      jetBlockValue φ η m (extract.eval x) b * jetBlockValue φ η m (extract.eval y) b) →
    ∀ k, recover.eval z k = openConv R n x y k

/-- Assemble all the blocks in parallel and charge the common operand circuit
twice. The local monic reductions and Karatsuba projections are included in
the per-block budget. -/
theorem exists_openConvolution_of_jetBlocks (φ : R →+* S) (η : S) (m : B → S[X])
    (jets : ∀ b, JetCircuitsOver φ η (m b) (e b) (h b)) {a d : ℕ}
    (extract : Circuit R (Fin n) (JetBlockInput e h) a)
    (recover : Circuit R (JetBlockOutput e h) (Fin (2*n-1)) d)
    (correct : RecoversFromJetProducts φ η m extract recover) :
    ∃ p : OpenConvolution R n (B × Fin 3) (jetBlockLength e h), p.RealizesMultiple 1 ∧
      p.linearCost ≤ 2*a + d + ∑ b, (2*(2*e b*h b) + 3*(2*(2*e b*h b)-1) +
        h b*(6*(2*integralConvolutionCost (e b)+e b)+2*e b)) := by
  classical
  choose u v encoder decoder hu hv hproduct using jets
  obtain ⟨i, hi, enc, henc⟩ := circuit_family encoder
  obtain ⟨o, ho, dec, hdec⟩ := circuit_family decoder
  obtain ⟨ii, hii, input, hinput⟩ := circuit_comp extract enc
  let input' : Circuit R (Fin n) (Σ j, Fin (jetBlockLength e h j)) ii :=
    ⟨input.program, fun k => input.output ⟨k.1.1, k.2, k.1.2⟩⟩
  let idx (k : Σ b, Σ _ : Fin (2*(2*e b*h b)-1), Fin 3) :
      Σ j, Fin (2*jetBlockLength e h j-1) := ⟨(k.1,k.2.2), k.2.1⟩
  let dec' := dec.rewire (fun k => (1, idx k)) (fun k => (1,k))
  obtain ⟨oo, hoo, output, houtput⟩ := circuit_comp dec' recover
  let p : OpenConvolution R n (B × Fin 3) (jetBlockLength e h) :=
    ⟨ii,oo,input',output⟩
  refine ⟨p, ?_, ?_⟩
  · intro x y k
    change output.eval (p.children x y) k = _
    rw [houtput, one_mul]
    refine correct x y _ ?_ k
    intro b
    have hinput' (x : Fin n → R) (b : B) (j : Fin 3) (t : Fin (2*e b*h b)) :
        input'.eval x ⟨(b,j),t⟩ = (encoder b).eval (fun i => extract.eval x ⟨b,i⟩) ⟨t,j⟩ := by
      change input.eval x ⟨b, t, j⟩ = _
      simp only [hinput, henc, Function.comp_def]
    have hchildren (j : Fin 3) (t : Fin (2*(2*e b*h b)-1)) :
        p.children x y ⟨(b,j),t⟩ =
          openConv R (2*e b*h b) (fun k => (encoder b).eval (fun i => extract.eval x ⟨b,i⟩) ⟨k,j⟩)
            (fun k => (encoder b).eval (fun i => extract.eval y ⟨b,i⟩) ⟨k,j⟩) t := by
      change openConv R (2*e b*h b) (fun k => input'.eval x ⟨(b,j),k⟩)
        (fun k => input'.eval y ⟨(b,j),k⟩) t = _
      simp only [hinput']
    simpa only [dec', Circuit.eval_rewire, one_mul, Function.comp_def, hdec, idx, hchildren,
      jetBlockValue] using
      (show jetOutputValueOver φ η (m b) (fun t => (decoder b).eval
        (fun k => p.children x y (idx ⟨b,k⟩)) t) = _ from by
        simpa only [idx, hchildren, Function.comp_def, jetBlockValue] using
          hproduct b (fun i => extract.eval x ⟨b,i⟩) (fun i => extract.eval y ⟨b,i⟩))
  · change 2*ii+oo ≤ _
    have H : 2*(∑ b, u b) + (∑ b, v b) ≤
        ∑ b, (2*(2*e b*h b) + 3*(2*(2*e b*h b)-1) +
          h b*(6*(2*integralConvolutionCost (e b)+e b)+2*e b)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun b _ => by have := hu b; have := hv b; omega
    omega

end FiniteFourier
end LinearAlgebra
end OAI
