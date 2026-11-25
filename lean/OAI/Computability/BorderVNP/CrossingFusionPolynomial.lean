import OAI.Computability.BorderVNP.CrossingFusionBinary
import OAI.Computability.BorderVNP.CrossingSplitSpecialization
import OAI.Computability.BorderVNP.CrossingRankMasks

/-!
# Expanding a fused side polynomial by its signed local paths

The terminal words, mode labels and intermediate occupation masks may all
be guessed. The monomial selects their terminal words and the bridge word
determined by the modes and the final rank. This form avoids guessing any
unconstrained auxiliary bits on the bridge.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open VPVNP.Crossing MvPolynomial

variable {m d p : ℕ}

/-- The external tensor entries with terminal and bridge groups in a single index set. -/
noncomputable def binarySideTensor (R : Type*) [CommRing R] (w : WireStates (leastEnergy m) (2^m))
    (addr : CutBit d (2*leastEnergy m) (stateCountAt (d*leastEnergy m)) ↪ Fin p × Fin m)
    (left : Bool) (b : Fin d → Bool) (a : (Fin d ⊕ Fin p) → Fin (2^m)) : R :=
  (binarySide w addr left b (a ∘ Sum.inl) (a ∘ Sum.inr) : R)

/-- Each terminal or bridge word chooses one variable in its own group. -/
noncomputable def sideMonomial (R : Type*) [CommRing R] (x : Fin d → Fin (2^m))
    (u : Fin p → Fin (2^m)) : MvPolynomial ((Fin d ⊕ Fin p) × Fin (2^m)) R :=
  (∏ i, X (Sum.inl i,x i)) * ∏ i, X (Sum.inr i,u i)

private theorem sum_extend_coeff {I J R : Type*} [Fintype I] [Fintype J] [CommRing R]
    (e : I ↪ J) (a : I → ℤ) (g : J → R) :
    (∑ j, ((Function.extend e a (fun _ => 0) j : ℤ) : R) * g j) =
      ∑ i, (a i : R) * g (e i) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)),
    Finset.sum_image e.injective.injOn]
  · simp only [e.injective.extend_apply]
  · intro j _ hj
    have h : ¬ ∃ i, e i = j := by simpa using hj
    simp only [Function.extend_apply' _ _ _ h, Int.cast_zero, zero_mul]

/-- Product of signed local entries for one complete assignment of all the
state cuts, including the state whose rank is transmitted. -/
noncomputable def chainWeight (w : WireStates (leastEnergy m) (2^m)) (left : Bool)
    (b : Fin d → Bool) (x : Fin d → Fin (2^m)) (j : Fin d → Fin (2*leastEnergy m))
    (z : (i : Fin (d+1)) → Fin (stateCountAt (i.val * leastEnergy m))) : ℤ :=
  ∏ i : Fin d, sideFactor (numberedStep w rankedStates i.val) left
    (b i.rev) (x i.rev) (j i.rev) (z i.castSucc) (z i.succ)

/-- The fused side polynomial is exactly the sum of signed path weights times
the monomials emitted by those paths. Occupation states remain shared between
adjacent factors. The transmitted state is the last one. -/
theorem binarySide_polynomial (R : Type*) [CommRing R] (w : WireStates (leastEnergy m) (2^m))
    (addr : CutBit d (2*leastEnergy m) (stateCountAt (d*leastEnergy m)) ↪ Fin p × Fin m)
    (left : Bool) (b : Fin d → Bool) :
    sidePolynomial (binarySideTensor R w addr left b) =
    ∑ x : Fin d → Fin (2^m), ∑ j : Fin d → Fin (2*leastEnergy m),
      ∑ z : (i : Fin (d+1)) → Fin (stateCountAt (i.val * leastEnergy m)),
        (chainWeight w left b x j z : MvPolynomial _ R) *
          sideMonomial R x (binaryBridge addr (j,z (Fin.last d))) := by
  classical
  rw [sidePolynomial]
  let term (a : (Fin d ⊕ Fin p) → Fin (2^m)) : MvPolynomial _ R :=
    C (binarySideTensor R w addr left b a) * ∏ i, X (i, a i)
  let A := Fin d ⊕ Fin p → Fin (2^m)
  have allInputs : @Finset.univ A (@Pi.instFintype _ _ (fun a b => Classical.propDecidable (a=b))
      (instFintypeSum _ _) (fun _ => Fin.fintype _)) = (Finset.univ : Finset A) := by
    ext a
    simp
  rw [allInputs]
  change ∑ a, term a = _
  rw [← (Equiv.sumArrowEquivProdArrow (Fin d) (Fin p) (Fin (2^m))).symm.sum_comp term,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  let e := Function.Embedding.mk _ (binaryBridge_injective addr)
  have hsum : (∑ u : Fin p → Fin (2^m),
      (binarySide w addr left b x u : MvPolynomial _ R) * sideMonomial R x u) =
      ∑ v, (fusedSide (numberedStep w rankedStates) left d b x v.1 v.2 : MvPolynomial _ R) *
        sideMonomial R x (binaryBridge addr v) :=
    sum_extend_coeff e _ _
  simp only [term, Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk, binarySideTensor,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr, Fintype.prod_sum_type, map_intCast]
  rw [show (∑ u : Fin p → Fin (2^m), (binarySide w addr left b x u : MvPolynomial _ R) *
    ((∏ i, X (Sum.inl i, x i)) * ∏ i, X (Sum.inr i,u i))) = _ from hsum,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [← (Fin.snocEquiv (fun i : Fin (d+1) => Fin (stateCountAt (i.val * leastEnergy m)))).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  rw [fusedSide_paths, Int.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  simp only [chainWeight, Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_castSucc, Fin.snoc_last]

end Crossing

end BorderVNP
end Computability
end OAI
