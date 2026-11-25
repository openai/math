import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyCoordinates
import OAI.LinearAlgebra.FiniteFourier.ConvolutionEnvelope

/-! # Scaling a jet by an arbitrary prescribed jet

The three base-ring products become fixed-operand convolution circuits when one
jet is prescribed. The coordinate order is the same at both ends so successive
scalings and synchronized transform stages can use these circuits directly.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* S} {η : S}
  {m : S[X]} {e h : ℕ}

/-- A fixed multiplier on a degree-`e`, height-`h` jet, including the monic
reductions in both coordinates of the quadratic coefficient order. -/
theorem JetCircuitsOver.fixedMultiplier (jets : JetCircuitsOver φ η m e h)
    (basis : Function.Bijective (fun u : Fin 2 → R => φ (u 0) + η * φ (u 1)))
    (hm : m.Monic) (hd : m.natDegree = e) (he : 0 < e) (z : JetQuotient m h) :
    ∃ s ≤ 2*e*h + 3*integralConvolutionCost (2*e*h) + 3*(2*(2*e*h)-1) +
        h*(6*(2*integralConvolutionCost e+e)+2*e),
      ∃ p : Circuit R ((Fin 2 × Fin h) × Fin e) ((Fin 2 × Fin h) × Fin e) s,
        ∀ x, jetOutputValueOver φ η m (p.eval x) = z * jetOutputValueOver φ η m x := by
  obtain ⟨u,v,enc,dec,hu,hv,hprod⟩ := jets
  obtain ⟨y, hy⟩ := (jetOutputValueOver_bijective (h := h) φ η basis hm hd he).surjective z
  let arr (x : (Fin 2 × Fin h) × Fin e → R) (i : (Fin h × Fin e) × Fin 2) :=
    x ((i.2,i.1.1),i.1.2)
  have hval (x : (Fin 2 × Fin h) × Fin e → R) :
      jetQuotientValue m (quadraticJetArray φ η (fun i => arr x (i,0)) (fun i => arr x (i,1))) =
        jetOutputValueOver φ η m x := (jetOutputValueOver_eq_jetQuotientValue φ η m x).symm
  choose t ht child hchild using fun j : Fin 3 =>
    exists_fixed_convolution_circuit (2*e*h) (fun i => enc.eval (arr y) ⟨i,j⟩)
  obtain ⟨s, hs, fam, hfam⟩ := circuit_family child
  let L := enc.rewire (fun i => (1, ((i.2,i.1.1),i.1.2))) (fun i => (1,i))
  let F := fam.rewire (fun i => (1, (⟨i.2,i.1⟩ : Σ _ : Fin (2*e*h), Fin 3)))
    (fun o : Σ _ : Fin (2*(2*e*h)-1), Fin 3 => (1, ⟨o.2,o.1⟩))
  obtain ⟨s₁, hs₁, q, hq⟩ := circuit_comp L F
  obtain ⟨s₂, hs₂, r, hr⟩ := circuit_comp q dec
  have hsum : (∑ j : Fin 3, t j) ≤ 3*integralConvolutionCost (2*e*h) :=
    (Finset.sum_le_sum fun j _ => ht j).trans_eq (by simp)
  refine ⟨s₂, by omega, r, ?_⟩
  intro x
  have hscl (k : Σ _ : Fin (2*(2*e*h)-1), Fin 3) : q.eval x k =
      openConv R (2*e*h) (fun i => enc.eval (arr x) ⟨i,k.2⟩)
        (fun i => enc.eval (arr y) ⟨i,k.2⟩) k.1 := by
    simp only [hq, F, L, Circuit.eval_rewire, one_mul, hfam, hchild, Function.comp_def, arr]
  rw [hr, show q.eval x = _ from funext hscl, hprod, hval, hval, hy, mul_comm]

/-- The charge for one prescribed jet scaling is at most forty units of
the shorter-length envelope per rectangular base coefficient. -/
theorem JetCircuitsOver.fixedMultiplier_envelope (jets : JetCircuitsOver φ η m e h)
    (basis : Function.Bijective (fun u : Fin 2 → R => φ (u 0) + η * φ (u 1)))
    (hm : m.Monic) (hd : m.natDegree = e) (he : 0 < e) (hh : 0 < h) {cutoff : ℕ}
    (hc : 2*e*h ≤ cutoff) (z : JetQuotient m h) :
    ∃ s : ℕ, (s : ℝ) ≤ 40*e*h*convolutionEnvelope cutoff ∧
      ∃ p : Circuit R ((Fin 2 × Fin h) × Fin e) ((Fin 2 × Fin h) × Fin e) s,
        ∀ x, jetOutputValueOver φ η m (p.eval x) = z * jetOutputValueOver φ η m x := by
  obtain ⟨s, hs, p, hp⟩ := jets.fixedMultiplier basis hm hd he z
  refine ⟨s, ?_, p, hp⟩
  let E := convolutionEnvelope cutoff
  have hcost (i : ℕ) (hi : 0 < i) (hci : i ≤ cutoff) : (integralConvolutionCost i : ℝ) ≤ i*E := by
    simpa only [E, mul_comm (convolutionEnvelope cutoff)] using (div_le_iff₀ (by exact_mod_cast hi : (0:ℝ) < i)).mp
      (convolutionRate_le_envelope hi hci)
  have hp : 0 < 2*e*h := by positivity
  have he' : e ≤ 2*e*h :=
    (by omega : e ≤ 2*e).trans (Nat.le_mul_of_pos_right _ hh)
  have hi := hcost _ he (he'.trans hc)
  have hj := hcost _ hp hc
  push_cast at hj
  have hone : 1 ≤ E := convolutionEnvelope_one_le (hp.trans_le hc)
  have hreal : (s:ℝ) ≤ 2*e*h + 3*integralConvolutionCost (2*e*h) + 3*(2*(2*e*h)) +
      h*(6*(2*(integralConvolutionCost e:ℝ)+e)+2*e) := by
    have hnat : s ≤ 2*e*h + 3*integralConvolutionCost (2*e*h) + 3*(2*(2*e*h)) +
        h*(6*(2*integralConvolutionCost e+e)+2*e) := by omega
    exact_mod_cast hnat
  have hmul := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg (α := ℝ) h)
  have hbase := mul_le_mul_of_nonneg_left hone (mul_nonneg (Nat.cast_nonneg (α := ℝ) e)
    (Nat.cast_nonneg (α := ℝ) h))
  change (s:ℝ) ≤ 40*e*h*E
  linarith only [hreal, hmul, hbase, hj]

end FiniteFourier
end LinearAlgebra
end OAI
