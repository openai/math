import OAI.Computability.VPVNP.CompressorLabelEvaluator
import OAI.Computability.VPVNP.PairedChain

/-!
# The two coefficient identities used by the diagonal chain

The joint label algebra evaluates the primed contraction to the original
integer count, and its monomial evaluator reads the production and compressor
exponents together. Accumulating the exponents across pairs permits a single
application of the functional to the entire product in the evaluator tail.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open MvPolynomial JointLabelSystem LabelEvaluator
local instance chainPrimeFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩
/-- Finite enumeration of the slice ground field used in the joint coefficient evaluation. -/
noncomputable local instance chainGroundFintype (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) :=
  Fintype.ofFinite _
/-- Scalar action of the slice ground field on the ambient field through the chosen slice
embedding. -/
noncomputable local instance chainGroundAlgebra (p : Nat.Primes) (t d : ℕ) : Algebra (Ground p t d) (Ambient p) :=
  (SliceField.embed p.val (columnCountBound t d) (Ambient p)).toRingHom.toAlgebra

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable {n c : ℕ} (hn : 2 ≤ n) {p : Nat.Primes}
variable (M : Model p (B.compressorDegree n) (B.compressorEquations hn c))

/-- Grammar specialization in the algebra chosen for both compressor blocks. -/
noncomputable abbrev productionValues := M.labels ∘ leftIndex (Production n c) B.Entry

/-- The same slice point specifies all shrinking and refresh map entries. -/
noncomputable abbrev compressorValues := M.labels ∘ rightIndex (Production n c) B.Entry

theorem compressorValues_solution : B.IsSolution (B.compressorValues hn M) :=
  (B.compressorEvaluator_readback hn c M).2

/-- The primed chain uses the actual grammar solution in the common finite algebra. -/
theorem compressorEvaluator_primed {h Δ a r bucket w : ℕ} (program : UniversalMachine.Program)
    (hfit : BurstRAM.ProcessorInput.Fits program n r bucket w) (advice : CutSchedule.Bits a) :
    eval₂Hom (Int.castRingHom M.algebra) (B.productionValues hn M)
      (PairedChain.primed (h := h) (Δ := Δ) program hfit advice
        ⟨n - 1, by omega⟩ ⟨0, pow_pos (by omega) _⟩) =
      (PairedChain.original (h := h) (Δ := Δ) program hfit advice : M.algebra) :=
  PairedChain.primed_eq_original program hfit advice _ _ _ (B.compressorEvaluator_readback hn c M).1

/-- Evaluate a single monomial consisting of production labels and fixed
compressor labels. The coordinate numbering agrees with the joint equations. -/
theorem compressorEvaluator_monomial (width : ℕ) (μ : Production n c → ℕ) (ν : B.Entry → ℕ)
    (hμ : ∀ i, μ i < 2 ^ width) (hν : ∀ i, ν i < 2 ^ width) :
    (M.presentation.branchCount p.val width (joinAssignment μ ν) : ZMod p.val) =
      M.functional ((∏ i, (B.productionValues hn M i) ^ μ i) *
        ∏ i, (B.compressorValues hn M i) ^ ν i) := by
  have h e : joinAssignment μ ν e < 2 ^ width := by
    obtain ⟨i, rfl⟩ := (Fintype.equivFin (Production n c ⊕ B.Entry)).surjective e
    cases i with
    | inl v => simpa [joinAssignment] using hμ v
    | inr v => simpa [joinAssignment] using hν v
  rw [M.branchCount_mod width _ h]
  apply congrArg M.functional
  rw [← (Fintype.equivFin (Production n c ⊕ B.Entry)).prod_comp
    (fun i ↦ M.labels i ^ joinAssignment μ ν i)]
  rw [Fintype.prod_sum_type]
  simp [productionValues, compressorValues, leftIndex, rightIndex, joinAssignment]

/-- After the chain accumulates one pair's exponents at a time, the tail
counts precisely the functional applied to the product of all pair weights. -/
theorem compressorEvaluator_pair_product {I : Type*} [Fintype I] (width : ℕ)
    (μ : I → Production n c → ℕ) (ν : I → B.Entry → ℕ)
    (hμ : ∀ v, (∑ i, μ i v) < 2 ^ width) (hν : ∀ v, (∑ i, ν i v) < 2 ^ width) :
    (M.presentation.branchCount p.val width
      (joinAssignment (fun v ↦ ∑ i, μ i v) (fun v ↦ ∑ i, ν i v)) : ZMod p.val) =
      M.functional (∏ i, (∏ v, (B.productionValues hn M v) ^ μ i v) *
        ∏ v, (B.compressorValues hn M v) ^ ν i v) := by
  rw [B.compressorEvaluator_monomial hn M width _ _ hμ hν]
  apply congrArg M.functional
  rw [Finset.prod_mul_distrib]
  simp only [← Finset.prod_pow_eq_pow_sum]
  exact congrArg₂ (· * ·) Finset.prod_comm Finset.prod_comm

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
