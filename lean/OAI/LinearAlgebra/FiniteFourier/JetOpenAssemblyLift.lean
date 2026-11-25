import OAI.LinearAlgebra.FiniteFourier.ConvolutionJet
import OAI.LinearAlgebra.FiniteFourier.ConvolutionJetCircuitDescent
import OAI.LinearAlgebra.FiniteFourier.ConvolutionJetParallel
import OAI.LinearAlgebra.FiniteFourier.CircuitLinearity

/-! # Running scalar circuits on quadratic coordinates of jet-valued rows -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial
open scoped BigOperators

noncomputable section

variable {R S A I O T : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra S A]

/-- Evaluation is the sum of monomials in the coefficient and jet generators. -/
theorem jetQuotientValue_eq_sum (m : S[X]) {e h : ℕ} (x : JetArray S e h) :
    jetQuotientValue m x = ∑ t : Fin h × Fin e, algebraMap S (JetQuotient m h) (x t) *
      (algebraMap (AdjoinRoot m) _ (AdjoinRoot.root m ^ t.2.val) *
        AdjoinRoot.root (X ^ h) ^ t.1.val) := by
  simp only [jetQuotientValue, jetBivariate, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, map_sum,
    ← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    IsScalarTower.algebraMap_apply S (AdjoinRoot m) (JetQuotient m h), AdjoinRoot.algebraMap_eq,
    mul_assoc]

/-- Evaluating a rectangular coefficient array in the iterated quotient is linear
over the ground ring, for any coefficient modulus and jet height. -/
def jetQuotientLinear (m : S[X]) (e h : ℕ) : JetArray S e h →ₗ[S] JetQuotient m h where
  toFun := jetQuotientValue m
  map_add' x y := by
    simp only [jetQuotientValue_eq_sum, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    change jetQuotientValue m (fun t => a * x t) = a • jetQuotientValue m x
    simp only [jetQuotientValue_eq_sum, Algebra.smul_def, Finset.mul_sum, map_mul, mul_assoc]

/-- A linear interpretation of a row's slots commutes with applying a scalar
circuit to the columns. The resulting matrix acts by scalar extension. -/
theorem Circuit.linear_slots [Fintype I] {s : ℕ} (p : Circuit S I O s)
    (v : (T → S) →ₗ[S] A) (x : I → T → S) (o : O) :
    v (fun t => p.eval (fun i => x i t) o) =
      (p.matrix.map (algebraMap S A)).mulVec (fun i => v (x i)) o := by
  have h : (fun t => p.eval (fun i => x i t) o) = ∑ i, p.matrix o i • x i := by
    ext t
    simp [Circuit.eval_eq_mulVec, Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [h, map_sum]
  simp only [map_smul]
  simp [Matrix.mulVec, dotProduct, Algebra.smul_def]

/-- A base-ring circuit acts on a family of jet-valued rows. Each of the
`e*h` coefficient slots receives one quadratic descent of the scalar circuit. -/
theorem exists_jetArray_circuit [Fintype I] [Fintype O] (φ : R →+* S) (η : S)
    {c d : R} (hη : η^2 = φ c + η*φ d) (coords : ∀ s, ∃ a b : R, φ a + η*φ b = s)
    (m : S[X]) (e h : ℕ) {s : ℕ} (p : Circuit S I O s) :
    ∃ n ≤ e*h*(6*s+2*Fintype.card O),
    ∃ q : Circuit R (I × ((Fin h × Fin e) × Fin 2)) (O × ((Fin h × Fin e) × Fin 2)) n,
      ∀ x o, jetQuotientValue m (QuadraticDescent.decode φ η (fun w => q.eval x (o,w))) =
        (p.matrix.map (algebraMap S (JetQuotient m h))).mulVec
          (fun i => jetQuotientValue m (QuadraticDescent.decode φ η (fun w => x (i,w)))) o := by
  obtain ⟨a,ha,down,hdown⟩ := QuadraticDescent.circuit φ η hη coords p
  obtain ⟨n,hn,rows,hrows⟩ := circuit_rows (Fin h × Fin e) down
  let q := rows.rewire (fun w => (1, (w.2.1, (w.1,w.2.2))))
    (fun w : O × ((Fin h × Fin e) × Fin 2) => (1, (w.2.1, (w.1,w.2.2))))
  refine ⟨n, ?_, q, ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_fin] at hn
    exact hn.trans (by simpa [Nat.mul_comm e h] using Nat.mul_le_mul_left (h*e) ha)
  · intro x o
    let inputs (i : I) := QuadraticDescent.decode φ η (fun w => x (i,w))
    have H (t : Fin h × Fin e) :
        QuadraticDescent.decode φ η (fun w => q.eval x (o,w)) t =
          p.eval (fun i => inputs i t) o := by
      have step := hdown (fun w : I × Fin 2 => x (w.1,t,w.2)) o
      change φ (down.eval _ (o,0)) + η * φ (down.eval _ (o,1)) =
        p.eval (fun i => φ (x (i,t,0)) + η * φ (x (i,t,1))) o at step
      simpa only [q, Circuit.eval_rewire, one_mul, hrows, QuadraticDescent.decode, inputs] using step
    rw [funext H]
    exact p.linear_slots (jetQuotientLinear m e h) inputs o

end

end FiniteFourier
end LinearAlgebra
end OAI
