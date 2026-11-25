import OAI.Computability.BorderVNP.DiagonalCommonField
import OAI.Computability.BorderVNP.BranchTableConstruction

/-! # The arithmetic branch of the signed family in the common coefficient field -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open MvPolynomial Crossing Branch
open scoped Classical

variable {K : Type*} [Field K] {D m : ℕ} {ι : Type} {G : PaidIdentity K D m}
variable {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}

/-- The entire signed target vector, using the variable numbering of the actual branch. -/
noncomputable abbrev signedTarget (E : Type*) [Field E] (k : ℕ)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) :=
  Int.castRingHom E ∘ coeffVector (k+1) (rename ord (Pstar (k+1)))

/-- The advised chart equations on the full signed universal table. -/
noncomputable def signedEquations (E : Type*) [Field E] (k s : ℕ)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (advice : CurveAdvice E (pairedTableParameters (k+1) s)) :=
  let n := k+1
  letI := Fintype.ofFinite (DegreeMonomial (Fin (2*n)) n)
  advice.equations (numberedTable E (2*n) k s) (signedTarget E k ord)
    (pairedDegreeExponent n) ((n+1)^(2*n))

/-- The finite extension, scalar advice and actual nonsingular geometric branch
used for every query at this length. -/
structure AdvisedBranch (R : CommonField G aux q k s ord) where
  /-- Finite extension in which all the advised rows are defined. -/
  E : IntermediateField R.E₀ (AlgebraicClosure R.E₀)
  [finite : Finite E]
  /-- Chosen chart, slicing scalars, coordinate pins and displacement. -/
  advice : CurveAdvice E (pairedTableParameters (k+1) s)
  degree : ∀ i, (signedEquations E k s ord advice i).totalDegree ≤ 2*k+3
  /-- The nonsingular function-field branch through the prescribed coefficients. -/
  branch : GeometricBranch (numberedTable E (2*(k+1)) k s) (signedTarget E k ord)
    (fun i => genericRow (signedEquations E k s ord advice i))
  [finiteResidue : Finite (IsLocalRing.ResidueField branch.place)]

attribute [instance] AdvisedBranch.finite AdvisedBranch.finiteResidue

private theorem log_product_bound {a b c n : ℕ} (h : n ≤ a * max b 1 * max c 1) :
    Nat.clog 2 n ≤ Nat.clog 2 a + Nat.clog 2 b + Nat.clog 2 c := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add, pow_add]
  refine h.trans (Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) ?_) ?_)
  · exact max_le (Nat.le_pow_clog (by decide) _) Nat.one_le_two_pow
  · exact max_le (Nat.le_pow_clog (by decide) _) Nat.one_le_two_pow

/-- The table closure from the common specialization supplies one finite branch.
Its field bit length costs only the initial constants and the two bounded
geometric choices. -/
theorem CommonField.exists_advisedBranch (R : CommonField G aux q k s ord) :
    ∃ chart : AdvisedBranch R, Nat.clog 2 (Nat.card chart.E) ≤
      Nat.clog 2 (Nat.card R.E₀) + pairedChoiceBitBudget (k+1) s := by
  let := Fintype.ofFinite R.E₀
  have hc := numbered_branch_of_tableClosure R.E₀ (AlgebraicClosure R.E₀)
    k s (rename ord (Pstar (k+1))) R.closure
  obtain ⟨E,hE,hcard,a,deg,b,hb⟩ := hc
  let chart : AdvisedBranch R := ⟨E,a,deg,b⟩
  refine ⟨chart,?_⟩
  have ht := log_product_bound hcard
  change Nat.clog 2 (Nat.card E) ≤ _
  rw [Nat.card_eq_fintype_card (α := R.E₀)]
  dsimp only [pairedChoiceBitBudget]
  rw [show 2*(k+1)-1 = 2*k+1 by omega, show 2*k+1+1 = 2*k+2 by omega, ← Nat.add_assoc]
  exact ht

/-- The same chosen entries, cast into the finite chart field, satisfy every
joint relation from the original shortening and cube. -/
theorem AdvisedBranch.preserves_tables {R : CommonField G aux q k s ord}
    (chart : AdvisedBranch R) :
    PreservesTables G aux (algebraMap R.E₀ chart.E ∘ R.entry) := by
  intro f hf
  have h := congrArg (algebraMap R.E₀ chart.E) (R.preserves f hf)
  rw [map_zero] at h
  have hc : (algebraMap R.E₀ chart.E).comp (Int.castRingHom R.E₀) =
      Int.castRingHom chart.E := Subsingleton.elim _ _
  simpa only [map_eval₂Hom, hc, Function.comp_def] using h

end Diagonal

end BorderVNP
end Computability
end OAI
