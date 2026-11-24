import OAI.Computability.VPVNP.CompressorEvaluatorChain
import OAI.Computability.VPVNP.FixedLabelReadback

/-!
# Proposition 9.1 for the joint compressor evaluator

The label assignment, scalar field and normalized functional all come from
one slice model of the actual grammar and compressor equations. The two
machine-count inputs are the weighted path identity for each primed pair and
the modular path count of the evaluator on its initial exponent tape. The
integer count used for the contradiction is the original paired chain.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open MvPolynomial JointLabelSystem LabelEvaluator CutSchedule ExponentTrace UniversalMachine
open scoped Classical

local instance pairedPrimeFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩
/-- Finite enumeration of the slice ground field used to instantiate the paired evaluator's
matrix-coordinate arguments. -/
noncomputable local instance pairedGroundFintype (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) := Fintype.ofFinite _

/-- The algebra structure on the ambient field induced by the designated embedding of the
finite slice ground field. -/
noncomputable local instance pairedGroundAlgebra (p : Nat.Primes) (t d : ℕ) : Algebra (Ground p t d) (Ambient p) :=
  (SliceField.embed p.val (columnCountBound t d) (Ambient p)).toRingHom.toAlgebra
/-- Classical equality of productions for the finite choices and coefficient comparisons of the
paired evaluator argument. -/
noncomputable local instance pairedProductionDecEq (n c : ℕ) : DecidableEq (Production n c) := Classical.decEq _

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable {n c : ℕ}

/-- One cell of the physical increment array in dense parser order, followed
by compressor occurrence counts in the fixed motif order. -/
noncomputable def denseExponent (μ : Production n c → ℕ) (ν : B.Entry → ℕ)
    (i : Fin (FixedRows.productionCount n c + Fintype.card B.Entry)) : ℕ :=
  (finSumFinEquiv.symm i).elim (μ ∘ (PrimedStackRAM.labelIndex n n _).symm)
    (ν ∘ (Fintype.equivFin B.Entry).symm)

/-- Applying the dense-to-formal coordinate permutation recovers the corresponding
production or compressor count in the joint assignment. -/
theorem denseExponent_labelOrder (μ : Production n c → ℕ) (ν : B.Entry → ℕ)
    (i : Fin (FixedRows.productionCount n c + Fintype.card B.Entry)) :
    joinAssignment μ ν (FixedRows.labelOrder B.Entry n c i) = B.denseExponent μ ν i := by
  obtain ⟨(v | v), rfl⟩ := finSumFinEquiv.surjective i <;>
    simp [FixedRows.labelOrder, joinAssignment, denseExponent]

/-- The decoded order-advice word names the formal coordinate at which the
evaluator must receive this dense exponent. -/
theorem denseExponent_orderAdvice (μ : Production n c → ℕ) (ν : B.Entry → ℕ)
    (i : Fin (FixedRows.productionCount n c + Fintype.card B.Entry)) :
    let w := ((RAMSerialization.arrayBits _ _).symm (FixedRows.orderAdvice B.Entry n c) i).val
    ∃ j : Fin (B.compressorLabelCount c n), j.val = w ∧
      joinAssignment μ ν j = B.denseExponent μ ν i := by
  exact ⟨FixedRows.labelOrder B.Entry n c i, (FixedRows.orderAdvice_lookup ..).symm,
    B.denseExponent_labelOrder μ ν i⟩

/-- Groupwise exponent accumulation commutes with numbering the joint label list. -/
theorem sum_joinedExponents {I : Type*} [Fintype I] (μ : I → Production n c → ℕ) (ν : I → B.Entry → ℕ) :
    (fun j => ∑ i, joinAssignment (μ i) (ν i) j) =
      joinAssignment (fun v => ∑ i, μ i v) (fun v => ∑ i, ν i v) := by
  funext j
  obtain ⟨(v | v), rfl⟩ := (Fintype.equivFin (Production n c ⊕ B.Entry)).surjective j <;>
    simp [joinAssignment]

/-- The parser nominates every production using exactly the paper's `2r` bits. -/
abbrev PairNomination (n c r : ℕ) := Production n c → Fin (2 ^ (2*r))

private theorem pairSum_lt {h r Z : ℕ} (hZ : h + 2*r ≤ Z) (v : Fin (2^h) → ℕ)
    (hb : ∀ i, v i < 2^(2*r)) : (∑ i, v i) < 2^Z := by
  calc
    (∑ i, v i) < ∑ _ : Fin (2^h), 2^(2*r) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hb i)
    _ = 2^(h+2*r) := by simp [pow_add]
    _ ≤ 2^Z := Nat.pow_le_pow_right (by decide) hZ

variable {h Δ a r bucket w Z : ℕ} {p : Nat.Primes} (hn : 2 ≤ n)
variable (M : Model p (B.compressorDegree n) (B.compressorEquations hn c))
variable (program : UniversalMachine.Program) (hfit : BurstRAM.ProcessorInput.Fits program n r bucket w) (advice : Bits a)
variable {Path : Exterior h Δ → Fin (2^h) → PairNomination n c r → Type*}
variable [∀ ξ i μ, Fintype (Path ξ i μ)]

/-- An actual tail evaluator cannot satisfy the physical live-count identity
alongside the weighted compressor identities of Section 12. The original
primed site labels and the evaluation functional are read out of the chosen
model of the integer equations. -/
theorem pairedEvaluatorContradiction (hR : 4 * n ≤ 2^r) (hZ : h + 2*r ≤ Z)
    (ν : ∀ ξ i μ, Path ξ i μ → B.Entry → ℕ)
    (hν : ∀ ξ i μ q v, ν ξ i μ q v < 2^(2*r))
    (hpair : ∀ ξ i μ, ∑ q : Path ξ i μ, ∏ v, (B.compressorValues hn M v) ^ ν ξ i μ q v =
      (GrammarDiagonal.multiplicity (⟨n-1, by omega⟩ : Fin n)
        (⟨0, pow_pos (by omega) _⟩ : Fin (n^(c+5))) (PairedChain.siteInput program hfit advice ξ i) μ : M.algebra))
    (E : UniversalMachine.Program) (initial : (Fin (B.compressorLabelCount c n) → ℕ) → Config E.extra)
    (htail : ∀ e, (∀ j, e j < 2^Z) → (paths E (2^h) (initial e) : ZMod p.val) =
      (M.presentation.branchCount p.val Z e : ZMod p.val))
    (hlive : PairedChain.original (h := h) (Δ := Δ) program hfit advice = 1 +
      ∑ ξ : Exterior h Δ, ∑ μ : Fin (2^h) → PairNomination n c r, ∑ q : (i : Fin (2^h)) → Path ξ i (μ i),
        paths E (2^h) (initial (fun j => ∑ i, joinAssignment (fun v => (μ i v).val) (ν ξ i (μ i) (q i)) j))) : False := by
  let d : Fin n := ⟨n-1, by omega⟩
  let head : Fin (n^(c+5)) := ⟨0, pow_pos (by omega) _⟩
  let label (μ : PairNomination n c r) := ∏ v, (B.productionValues hn M v) ^ (μ v).val
  let coeff (ξ : Exterior h Δ) (i : Fin (2^h)) (μ : PairNomination n c r) : ℕ := GrammarDiagonal.multiplicity d head (PairedChain.siteInput program hfit advice ξ i) μ
  let gadget (ξ : Exterior h Δ) (i : Fin (2^h)) (μ : PairNomination n c r) (q : Path ξ i μ) := ∏ v, (B.compressorValues hn M v) ^ ν ξ i μ q v
  apply Diagonal.pairedChainCriterion (PairedChain.original program hfit advice) M.functional M.functional_one
    label coeff gadget hpair
  · rw [← B.compressorEvaluator_primed hn M program hfit advice]
    change (∑ ξ, ∏ i, ∑ μ, label μ * (coeff ξ i μ : M.algebra)) =
      eval₂Hom (Int.castRingHom M.algebra) (B.productionValues hn M)
        (∑ ξ : Exterior h Δ, ∏ i, PairCoefficient.jointPolynomial d head (PairedChain.siteInput program hfit advice ξ i))
    simp only [map_sum, map_prod]
    apply Finset.sum_congr rfl
    intro ξ _
    apply Finset.prod_congr rfl
    intro i _
    apply (PairCoefficient.evaluate_by_nominations d head _ _ (2*r) _).symm
    simpa only [PrimedInputRAM.Site, Fintype.card_prod, Fintype.card_fin, d] using
      PairCoefficient.pair_counter_capacity r n (by omega) hR
  · rw [hlive, Nat.cast_add, Nat.cast_one, Diagonal.evaluationMode]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro ξ _
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro q _
    let μ' i v := (μ i v).val
    let ν' i v := ν ξ i (μ i) (q i) v
    have hμsum (v) := pairSum_lt hZ (fun i => μ' i v) (fun i => (μ i v).isLt)
    have hνsum (v) := pairSum_lt hZ (fun i => ν' i v) (fun i => hν ξ i (μ i) (q i) v)
    rw [B.sum_joinedExponents μ' ν', htail]
    · exact B.compressorEvaluator_pair_product hn M Z μ' ν' hμsum hνsum
    · intro j
      obtain ⟨(v | v), rfl⟩ := (Fintype.equivFin (Production n c ⊕ B.Entry)).surjective j
      · simpa [joinAssignment] using hμsum v
      · simpa [joinAssignment] using hνsum v

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
