import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyLift
import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyScale

/-! # The operand basis of a quadratic jet algebra

The three power coordinates are ordered exactly as the operand encoder reads them.
In this basis the fixed-jet circuits realize the multiplication matrices used in
the restriction of each monomial layer.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial Module

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {m : S[X]} {e h : ℕ}

/-- Encoding a quadratic coefficient by a basis with entries `1, η` is bijective. -/
theorem bijective_quadraticEncoding_of_basis (η : S) (b : Basis (Fin 2) R S)
    (h0 : b 0 = 1) (h1 : b 1 = η) :
    Function.Bijective (fun t : Fin 2 → R => algebraMap R S (t 0) + η * algebraMap R S (t 1)) := by
  convert b.equivFun.symm.bijective using 1
  funext t
  simp [Basis.equivFun_symm_apply, Fin.sum_univ_two, h0, h1, Algebra.smul_def, mul_comm]

private def quadraticArrayLinear (η : S) (e h : ℕ) :
    (((Fin h × Fin e) × Fin 2) → R) →ₗ[R] JetArray S e h where
  toFun x := quadraticJetArray (algebraMap R S) η (fun i => x (i,0)) (fun i => x (i,1))
  map_add' x y := by ext i; simp [quadraticJetArray, mul_add]; ring
  map_smul' a x := by ext i; simp [quadraticJetArray, Algebra.smul_def]; ring

private theorem quadraticArrayLinear_bijective (η : S)
    (hb : Function.Bijective (fun t : Fin 2 → R => algebraMap R S (t 0) + η * algebraMap R S (t 1))) :
    Function.Bijective (quadraticArrayLinear (R := R) η e h) := by
  constructor
  · intro x y hxy
    funext ⟨i,q⟩
    exact congrFun (hb.injective (a₁ := fun d => x (i,d)) (a₂ := fun d => y (i,d))
      (congrFun hxy i)) q
  · intro y
    choose x hx using fun i => hb.surjective (y i)
    exact ⟨fun i => x i.1 i.2, funext hx⟩

/-- The basis indexed by jet degree, coefficient degree, and quadratic coordinate. -/
def jetOperandBasis (η : S) (hb : Function.Bijective
    (fun t : Fin 2 → R => algebraMap R S (t 0) + η * algebraMap R S (t 1)))
    (hm : m.Monic) (hd : m.natDegree = e) (he : 0 < e) (h : ℕ) :
    Basis ((Fin h × Fin e) × Fin 2) R (JetQuotient m h) :=
  Basis.ofEquivFun (LinearEquiv.ofBijective
    (((jetQuotientLinear m e h).restrictScalars R).comp (quadraticArrayLinear η e h))
    ((jetQuotientValue_bijective hm hd he).comp (quadraticArrayLinear_bijective η hb))).symm

variable (η : S) (hb : Function.Bijective
    (fun t : Fin 2 → R => algebraMap R S (t 0) + η * algebraMap R S (t 1)))
    (hm : m.Monic) (hd : m.natDegree = e) (he : 0 < e)

/-- Coordinate synthesis in the operand basis is exactly the jet value read by the encoder. -/
theorem jetOperandBasis_decode (x : (Fin h × Fin e) × Fin 2 → R) :
    (jetOperandBasis η hb hm hd he h).equivFun.symm x = jetOperandValue (algebraMap R S) η m x := by
  rw [jetOperandBasis, Basis.equivFun_ofEquivFun, LinearEquiv.symm_symm]
  rfl

/-- Each basis vector is the product of the three indicated generator powers. -/
theorem jetOperandBasis_apply (t : Fin h) (i : Fin e) (q : Fin 2) :
    jetOperandBasis η hb hm hd he h ((t,i),q) =
      algebraMap S (JetQuotient m h) (η ^ q.val) *
        (algebraMap (AdjoinRoot m) _ (AdjoinRoot.root m ^ i.val) *
          AdjoinRoot.root ((X : (AdjoinRoot m)[X]) ^ h) ^ t.val) := by
  rw [← Basis.equivFun_symm_single, jetOperandBasis_decode]
  have single (p : Fin h × Fin e) :
      quadraticJetArray (algebraMap R S) η
          (fun j => (Pi.single ((t,i),q) 1 : ((Fin h × Fin e) × Fin 2) → R) (j,0))
          (fun j => (Pi.single ((t,i),q) 1 : ((Fin h × Fin e) × Fin 2) → R) (j,1)) p =
        if p = (t,i) then η ^ q.val else 0 := by
    by_cases hp : p = (t,i) <;> fin_cases q <;>
      simp [quadraticJetArray, hp]
  simp only [jetOperandValue, jetQuotientValue, jetBivariate, single, Polynomial.map_sum,
    map_sum, ← C_mul_X_pow_eq_monomial, map_mul, map_pow,
    IsScalarTower.algebraMap_apply S (AdjoinRoot m) (JetQuotient m h),
    AdjoinRoot.algebraMap_eq, apply_ite, map_zero, mul_assoc]
  simp

private theorem jetOperand_matrix {s : ℕ} (z : JetQuotient m h)
    (q : Circuit R ((Fin h × Fin e) × Fin 2) ((Fin h × Fin e) × Fin 2) s)
    (hq : ∀ x, jetOperandValue (algebraMap R S) η m (q.eval x) =
      z * jetOperandValue (algebraMap R S) η m x) :
    let b := jetOperandBasis η hb hm hd he h
    q.matrix = (fun d u => b.repr (z * b u) d) := by
  intro b
  ext i j
  rw [Circuit.matrix_apply]
  have H := hq (Pi.single j 1)
  rw [← jetOperandBasis_decode η hb hm hd he, ← jetOperandBasis_decode η hb hm hd he,
    Basis.equivFun_symm_single] at H
  exact congrFun (b.equivFun.symm_apply_eq.mp H) i

/-- Fixed multiplication in the operand basis has the cost of the three fixed scalar
convolutions and their shared packing and reduction circuits. -/
theorem JetCircuitsOver.operandMatrix (jets : JetCircuitsOver (algebraMap R S) η m e h)
    (z : JetQuotient m h) :
    let b := jetOperandBasis η hb hm hd he h
    RealizableAtMost (fun d u => b.repr (z * b u) d)
      (2*e*h + 3*integralConvolutionCost (2*e*h) + 3*(2*(2*e*h)-1) +
        h*(6*(2*integralConvolutionCost e+e)+2*e)) := by
  obtain ⟨s,hs,q,hq⟩ := jets.operandScale hb hm hd he z
  exact ⟨s,hs,q,jetOperand_matrix η hb hm hd he z q hq⟩

/-- The uniform envelope version for descending a layer of monomial rows. -/
theorem JetCircuitsOver.operandMatrix_envelope (jets : JetCircuitsOver (algebraMap R S) η m e h)
    (hh : 0 < h) {s : ℕ} (hc : 2*e*h ≤ s) (z : JetQuotient m h) :
    let b := jetOperandBasis η hb hm hd he h
    RealizableAtMost (fun d u => b.repr (z * b u) d)
      ⌊40*(e : ℝ)*h*convolutionEnvelope s⌋₊ := by
  obtain ⟨g,hg,q,hq⟩ := jets.operandScale_envelope hb hm hd he hh hc z
  exact ⟨g,Nat.le_floor hg,q,jetOperand_matrix η hb hm hd he z q hq⟩

end

end FiniteFourier
end LinearAlgebra
end OAI
