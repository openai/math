import OAI.Computability.VPVNP.SliceArithmetic
import OAI.Computability.VPVNP.SliceEvaluator

/-!
# Recovering the evaluator's functional from its advised polynomial

Choose the minimal polynomial of the same power-basis generator used by the
evaluator. The quotient isomorphism sends the formal root to this generator,
so reading the first coefficient of an encoded field element computes the
prime-field coordinate used by the branch counter.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic

open Polynomial

/-- The low limb is the output of the final prime-field coordinate query. -/
def primeCoordinate {p e : ℕ} [NeZero e] (v : Vector p e) : Fin p := v 0

private theorem coord_map_value {p e : ℕ} [NeZero e]
    {K : Type*} [Field K] [Algebra (ZMod p) K] (pb : PowerBasis (ZMod p) K)
    (he : pb.dim = e) (f : (ZMod p)[X]) (φ : AdjoinRoot f ≃ₐ[ZMod p] K)
    (hφ : φ (AdjoinRoot.root f) = pb.gen) (v : Vector p e) :
    pb.basis.coord ⟨0, pb.dim_pos⟩ (φ (value f v)) = ((primeCoordinate v).val : ZMod p) := by
  subst e
  have h : φ (value f v) = ∑ j, ((v j).val : ZMod p) • pb.basis j := by
    simp only [value, map_sum, map_mul, AlgEquiv.commutes, map_pow, hφ, pb.basis_eq_pow,
      Algebra.smul_def]
  rw [h, map_sum]
  simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (0 : Fin pb.dim)]
  · simp [primeCoordinate]
  · intro i _ hi
    simp [hi]
  · simp

/-- Select one binary description and one field isomorphism that realize
the evaluator's specified coordinate on all coefficient vectors at once. -/
theorem exists_compatible_advice (p N : ℕ) [Fact p.Prime] [Fintype (SliceField.FieldOf p N)] :
    let e := SliceField.extensionDegree p N
    let K := SliceField.FieldOf p N
    ∃ c : Vector p e, ∃ φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K,
      modulus c = SliceField.polynomialOfBits p e (encode c) ∧ Irreducible (modulus c) ∧
      ∀ v : Vector p e, SliceEvaluator.primeCoordinate p K (φ (value (modulus c) v)) =
        ((v ⟨0, Nat.succ_pos _⟩).val : ZMod p) := by
  let e := SliceField.extensionDegree p N
  let K := SliceField.FieldOf p N
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod p) K
  let f := minpoly (ZMod p) pb.gen
  have he : pb.dim = e := pb.finrank.symm.trans (GaloisField.finrank p (Nat.succ_ne_zero _))
  have hf : f.natDegree = e := pb.natDegree_minpoly.trans he
  let c : Vector p e := fun i => (ZMod.finEquiv p).symm (f.coeff i.val)
  have hc : modulus c = f := by
    simp only [modulus, c, cast_val_eq_finEquiv, RingEquiv.apply_symm_apply]
    have hm : f.Monic := minpoly.monic pb.isIntegral_gen
    conv_rhs => rw [hm.as_sum, hf]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i) e
  let φ := AdjoinRoot.equiv' (modulus c) pb
    (by change aeval (AdjoinRoot.root (modulus c)) f = 0; rw [← hc, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
    (by rw [hc]; exact minpoly.aeval _ _)
  have hφ : φ (AdjoinRoot.root (modulus c)) = pb.gen := by
    simp only [φ, AdjoinRoot.equiv'_apply]
    apply AdjoinRoot.liftAlgHom_root
  have : NeZero e := ⟨Nat.succ_ne_zero _⟩
  refine ⟨c, φ, ?_, hc ▸ minpoly.irreducible pb.isIntegral_gen, fun v => ?_⟩
  · simpa only [ofBits_encode] using modulus_ofBits (encode c)
  · exact coord_map_value pb he _ φ hφ v

end SliceArithmetic

end VPVNP
end Computability
end OAI
