import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicDeformationProduct
import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicDeformationTaylor
import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyMatrix

/-! # Coordinate circuits for deformation stages

The two Taylor changes can change the number of jet coefficients. A row of either
change is independent of all other addresses. Each tensor generator scaling requires
one fixed jet multiplication at each address.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial Matrix

variable {R S I σ : Type*} [CommRing R] [CommRing S]

/-- A circuit on operand-order coordinate arrays implementing a map between two jet heights. -/
def JetStage (φ : R →+* S) (η : S) (M : S[X]) (e n N : ℕ)
    (f : (I → JetQuotient M n) → (I → JetQuotient M N)) (C : ℝ) : Prop :=
  ∃ g : ℕ, (g : ℝ) ≤ C ∧
    ∃ p : Circuit R (I × ((Fin n × Fin e) × Fin 2)) (I × ((Fin N × Fin e) × Fin 2)) g,
      ∀ x, jetOperandArray φ η M (p.eval x) = f (jetOperandArray φ η M x)

variable {φ : R →+* S} {η : S} {M : S[X]} {e n N H : ℕ}

theorem JetStage.comp {f : (I → JetQuotient M n) → (I → JetQuotient M N)}
    {g : (I → JetQuotient M N) → (I → JetQuotient M H)} {a b : ℝ}
    (hf : JetStage φ η M e n N f a) (hg : JetStage φ η M e N H g b) :
    JetStage φ η M e n H (g ∘ f) (a+b) := by
  obtain ⟨u, hu, p, hp⟩ := hf
  obtain ⟨v, hv, q, hq⟩ := hg
  obtain ⟨t, ht, c, hc⟩ := circuit_comp p q
  refine ⟨t, ?_, c, fun x => ?_⟩
  · exact (show (t:ℝ) ≤ (u:ℝ)+v by exact_mod_cast ht).trans (add_le_add hu hv)
  · simp only [hc, hq, hp, Function.comp_apply]

theorem JetStage.of_matrix [Fintype I] {A : Matrix I I (JetQuotient M n)} {c : ℝ}
    (h : JetMatrixCircuit φ η M e n A c) : JetStage φ η M e n n (A *ᵥ ·) c := h

/-- Run identical precision-changing circuits at all addresses, translating from decoder
order to operand order by free permutations. -/
theorem JetStage.of_rows [Fintype I] {f : JetQuotient M n → JetQuotient M N}
    {c : ℝ} (rows : ∃ (g : ℕ) (p : Circuit R ((Fin 2 × Fin n) × Fin e)
        ((Fin 2 × Fin N) × Fin e) g), (g:ℝ) ≤ c ∧
        ∀ x, jetOutputValueOver φ η M (p.eval x) = f (jetOutputValueOver φ η M x)) :
    JetStage φ η M e n N (fun x : I → _ => f ∘ x) ((Fintype.card I : ℝ)*c) := by
  obtain ⟨g,p,hg,hp⟩ := rows
  obtain ⟨t,ht,q,hq⟩ := circuit_rows I p
  let out := q.rewire (fun j => (1, (j.1,(j.2.1.2,j.2.2),j.2.1.1)))
    (fun j : I × ((Fin N × Fin e) × Fin 2) => (1, (j.1,(j.2.2,j.2.1.1),j.2.1.2)))
  refine ⟨t, ?_, out, fun x => funext fun i => ?_⟩
  · exact (show (t:ℝ) ≤ (Fintype.card I:ℝ)*g by exact_mod_cast ht).trans
      (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _))
  · have dec {h : ℕ} (y : (Fin h × Fin e) × Fin 2 → R) :
        jetOperandValue φ η M y = jetOutputValueOver φ η M (fun j => y ((j.1.2,j.2),j.1.1)) :=
      (jetOutputValueOver_eq_jetQuotientValue φ η M (fun j : (Fin 2 × Fin h) × Fin e => y ((j.1.2,j.2),j.1.1))).symm
    simp only [jetOperandArray, Function.comp_apply, dec, out, Circuit.eval_rewire, one_mul, hq, hp]

/-- Shift each short input to the zero-centered long jet before multiplying. -/
theorem jetStage_inputShift [Fintype I] (φ : R →+* S) (η : S) (m : S[X]) (e r H : ℕ)
    (hr : 0 < r) {cutoff : ℕ} (hc : 2*r ≤ cutoff) :
    JetStage φ η m e r H (fun x : I → _ => (specialize 0 H ∘ liftJet 1 r) ∘ x)
      ((Fintype.card I : ℝ) * (8*e*r*(1+Real.logb 2 r)*convolutionEnvelope cutoff)) :=
  JetStage.of_rows (exists_jet_input_shift_circuit φ η m e r H hr hc)

/-- Shift each long product to center one and read its first `r` coefficients. -/
theorem jetStage_outputShift [Fintype I] (φ : R →+* S) (η : S) (m : S[X]) (e H r : ℕ)
    (hH : 0 < H) {cutoff : ℕ} (hc : 2*H ≤ cutoff) :
    JetStage φ η m e H r (fun x : I → _ => readAtOne H r ∘ x)
      ((Fintype.card I : ℝ) * (8*e*H*(1+Real.logb 2 H)*convolutionEnvelope cutoff)) :=
  JetStage.of_rows (exists_jet_output_shift_circuit φ η m e H r hH hc)

variable [Fintype σ] [DecidableEq σ]

/-- A binomial generator change on jet arrays is a single diagonal layer, with the
product of all its axis multipliers already combined. -/
theorem Dyadic.scale_stage (width : σ → ℕ) (w : σ → (JetQuotient M n)ˣ)
    (jets : JetCircuitsOver φ η M e n)
    (basis : Function.Bijective (fun u : Fin 2 → R => φ (u 0) + η * φ (u 1)))
    (hm : M.Monic) (hd : M.natDegree = e) (he : 0 < e) (hn : 0 < n)
    {cutoff : ℕ} (hc : 2*e*n ≤ cutoff) :
    JetStage φ η M e n n (scale width w)
      ((Fintype.card (Address width) : ℝ)*(40*e*n*convolutionEnvelope cutoff)) := by
  let weights (k : Address width) := ∏ i, (w i : JetQuotient M n) ^ (k i).val
  choose cost bound circuit correct using fun k =>
    jets.operandScale_envelope basis hm hd he hn hc (weights k)
  obtain ⟨t, ht, family, hfamily⟩ := circuit_family circuit
  let q := family.rewire (fun j => (1, (j.1,j.2)))
    (fun j : Address width × ((Fin n × Fin e) × Fin 2) => (1, ⟨j.1,j.2⟩))
  refine ⟨t, ?_, q, fun x => funext fun k => ?_⟩
  · have H : (t:ℝ) ≤ ∑ i, (cost i : ℝ) := by exact_mod_cast ht
    exact H.trans (by simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => bound i)
  · have hv : (fun j => q.eval x (k,j)) = (circuit k).eval (fun j => x (k,j)) := by
      funext j
      simp [q, Circuit.eval_rewire, hfamily, Function.comp_def]
    change jetOperandValue φ η M (fun j => q.eval x (k,j)) = _
    rw [hv, correct]
    rfl

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
