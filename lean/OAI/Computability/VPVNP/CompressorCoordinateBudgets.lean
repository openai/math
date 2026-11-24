import OAI.Computability.VPVNP.CompressorReaderBudgets
import OAI.Computability.VPVNP.RankQueryPrepareResources
import OAI.Computability.VPVNP.RankQueryReaderFits

/-!
# Uniform coordinate-reader resources for the compressor evaluator

The base matrix and the prepared Frobenius or label target share the raw
entry budget. The common address width also covers every weighted-Gram
rank query in both orientations. The bounds below are chosen before the
prime, affine slice and entry ordinals.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open LabelEvaluator JointLabelSystem RadicalCertificate.MonomialIndex RankQuery.Stack.Coordinate
open ConcreteResources

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Word width required by the compressor's coordinate reader plan at the given characteristic,
exponent bound and input length. -/
noncomputable def coordinateWidth (q c n : ℕ) := planWidth (B.compressorReaderPlan q c n)

theorem coordinateWidth_polynomial (q c : ℕ) : PolynomiallyBounded (B.coordinateWidth q c) :=
  (planSizes (B.compressorReaderWidths q c).1).2.2

local instance coordinateBudgetsPrimeFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩

/-- All numerical premises for the physical coordinate query at the prime
selected for this length, including each operation's powered target. -/
theorem compressorCanonicalFits (q c : ℕ) {n : ℕ} (hn : 2 ≤ n) (p : Nat.Primes)
    [DecidableEq (Ground p (B.compressorLabelCount c n) (B.compressorDegree n))]
    (model : Model p (B.compressorDegree n) (B.compressorEquations hn c))
    (hq : q ≠ 0 → p.val = q) (hz : q = 0 → p.val ≤ 2^(B.compressorPrimeBits c n))
    {w : ℕ} (hw : B.coordinateWidth q c n ≤ w) (sp ex : ℕ) :
    let plan := B.compressorReaderPlan q c n
    let data := model.queryData (B.compressorCoeff hn c)
    let degree := B.readerDegreeBudget q c n
    let limb := B.readerLimbBudget q c n
    let e := SliceField.extensionDegree p.val (columnCountBound (B.compressorLabelCount c n) (B.compressorDegree n))
    CanonicalFits data (planDepth plan) w limb e (plan.live degree limb w sp)
      (plan.armSpace degree limb w sp) (plan.readTime degree limb w sp ex) ∧ SliceArithmetic.Word.workingWidth p.val ≤ limb := by
  obtain ⟨covers,he,hv⟩ := B.compressorReaderCovers q c hn p model hq hz
  exact ⟨canonicalFits covers hw he le_rfl sp ex,hv⟩

/-- The physical coefficient-counting leaf must fit the same raw budget for
every prime, field representation, and input length. -/
def SignedCallFits (q c : ℕ) (w signedSpace signedExp : ℕ → ℕ) : Prop :=
  ∀ n (hn : 2 ≤ n) (p e v : ℕ), e ≤ B.readerDegreeBudget q c n → v ≤ B.readerLimbBudget q c n →
    let layout := JointScalar.Leaf.layout B.Entry B.EquationIndex B.equation c hn (w n) p e v
    let counter := JointScalar.checker B.Entry B.EquationIndex B.equation c hn (w n)
    let bank := JointScalar.Leaf.bankSize layout (w n) (B.compressorLabelCount c n*w n)
    let work := JointScalar.Leaf.localCost layout bank
    max (UniversalCountStack.stackLimit counter) bank + work ≤ signedSpace n ∧
      2*(2^layout.witnessBits * UniversalCountStack.perChoice counter) + work ≤ 2^(signedExp n)

/-- Space and time budget for a prepared compressor coordinate query, combining the reader
plan's depth, address range, arithmetic sizes and label count. -/
noncomputable def coordinateBudget (P H K : Type) [Fintype P] [Fintype H] [Fintype K]
    (q c n w signedSpace signedExp : ℕ) : Cost.Budget :=
  let plan := B.compressorReaderPlan q c n
  let e := B.readerDegreeBudget q c n
  let v := B.readerLimbBudget q c n
  let A := plan.live e v w signedSpace
  let S := plan.armSpace e v w signedSpace
  let T := plan.readTime e v w signedSpace signedExp
  preparedMaximum P H K plan.addressLimit (planDepth plan) w e v T A S T (B.compressorLabelCount c n)

/-- A single length-indexed budget dominates the complete mounted scalar
reader, including its Cramer setup and its recursive calls to the Macaulay
coefficient reader. It allows any polynomial enlargement of the address
width needed by the enclosing evaluator. -/
theorem coordinateBudgets (P H K : Type) [Fintype P] [Fintype H] [Fintype K]
    (q c : ℕ) {w : ℕ → ℕ} (hw : PolynomiallyBounded w) :
    ∃ signedSpace signedExp : ℕ → ℕ, PolynomiallyBounded signedSpace ∧ PolynomiallyBounded signedExp ∧
      B.SignedCallFits q c w signedSpace signedExp ∧
      Cost.Feasible (fun n => B.coordinateBudget P H K q c n (w n) (signedSpace n) (signedExp n)) := by
  obtain ⟨sp,ex,hsp,hex,hA,hS,hT,fits⟩ := B.compressorRawReaderBudgets q c hw
  obtain ⟨hraw,he,hv⟩ := B.compressorReaderWidths q c
  obtain ⟨hlim,hd,_⟩ := planSizes hraw
  exact ⟨sp,ex,hsp,hex,fits,preparedMaximum_feasible P H K hlim hd hw he hv hT hA hS hT
    (B.compressorLabelCount_polynomial c)⟩

/-- For every concrete slice covered by the plan, the actual mounted
reader budget fits the length-only maximum. The finite box covers the
order of the square minor even when the augmented matrix is rectangular. -/
theorem coordinateBudget_covers (P H K : Type) [Fintype P] [Fintype H] [Fintype K]
    (q c n w signedSpace signedExp : ℕ) {F : Type} [Field F] [DecidableEq F]
    (data : QueryData (B.compressorReaderPlan q c n).arity
      ((B.compressorReaderPlan q c n).equations+(B.compressorReaderPlan q c n).pins) F)
    (hplan : (B.compressorReaderPlan q c n).Covers data) {e v : ℕ}
    (he : e ≤ B.readerDegreeBudget q c n) (hv : v ≤ B.readerLimbBudget q c n) :
    let plan := B.compressorReaderPlan q c n
    let nrows := (plan.equations+plan.pins)*size plan.arity data.multiplierDegree + size plan.arity data.pointBound
    let ncols := size plan.arity data.columnDegree
    let r := RankQuery.rankQuery (RankQuery.appendRows data.equations data.monomials)
    let ext := B.readerDegreeBudget q c n
    let limb := B.readerLimbBudget q c n
    let A := plan.live ext limb w signedSpace
    let S := plan.armSpace ext limb w signedSpace
    let T := plan.readTime ext limb w signedSpace signedExp
    let actual := preparedBudget P H K nrows ncols r (planDepth plan) w v e T A S T (B.compressorLabelCount c n)
    let bound := B.coordinateBudget P H K q c n w signedSpace signedExp
    actual.time ≤ bound.time ∧ actual.space ≤ bound.space := by
  obtain ⟨hr,hc,ho,_⟩ := plan_query_shapes hplan
  exact preparedMaximum_covers P H K hr hc ho he hv _ _ _ _ _ _ _

/-- The clock exponent and space exponent can be fixed together, before
the eventual input length and before every prime or model at that length. -/
theorem exists_coordinateClock (P H K : Type) [Fintype P] [Fintype H] [Fintype K] (q c : ℕ) :
    ∃ signedSpace signedExp : ℕ → ℕ, B.SignedCallFits q c (B.coordinateWidth q c) signedSpace signedExp ∧
      ∃ u N : ℕ, ∀ n ≥ N,
        let cost := B.coordinateBudget P H K q c n (B.coordinateWidth q c n) (signedSpace n) (signedExp n)
        cost.time ≤ 2^(n^u) ∧ cost.space ≤ n^u := by
  obtain ⟨sp,ex,_,_,hs,h⟩ := B.coordinateBudgets P H K q c (B.coordinateWidth_polynomial q c)
  exact ⟨sp,ex,hs,eventual_power h⟩

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
