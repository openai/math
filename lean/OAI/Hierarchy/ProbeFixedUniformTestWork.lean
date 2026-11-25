import OAI.Hierarchy.ProbeFixedUniformFailureExpr
import OAI.Hierarchy.ProbeFixedMarketRows

namespace OAI
/-! # Row counts and instruction work of the installed three-pass voting code -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

/-- One public constant bounds all three row expressions and their row multiplicities. -/
def testVoteFactor := 20+v.failureExprWork+GlobalTests.kinds (publicStages v.W) k+
  StripChart.treeRowsFactor (2^v.W) k v.sampler.degree v.depth

structure TestVoteBounds (T z : ℕ) (b : AttemptGate.TestBoard) : Prop where
  excessWork : b.excess.term.work ≤ T
  payloadWork : b.payload.term.work ≤ T
  discrepancyWork : b.discrepancy.term.work ≤ T
  excessRows : b.excess.rows ≤ T*2^z
  payloadRows : b.payload.rows ≤ T*2^z
  discrepancyRows : b.discrepancy.rows ≤ T*2^z

/-- The scored board already contains the original effective failure word. -/
theorem test_vote_bounds (P : v.Placement) (z width : ℕ) (a : Attempt) :
    TestVoteBounds v.testVoteFactor z (v.nativeFormats P z width a).board.tests := by
  let f:=v.nativeFormats P z width a
  let N:=Stages z (2^v.W)
  have shape : f.board.tests.excess.term.work=20 ∧ f.board.tests.payload.term.work=20 ∧
      f.board.tests.excess.rows=GlobalTests.rows z N k ∧ f.board.tests.payload.rows=GlobalTests.rows z N k := by
    cases a <;> exact ⟨rfl,rfl,rfl,rfl⟩
  have word : 20 ≤ v.testVoteFactor := by unfold testVoteFactor; omega
  have fail := v.failure_expr_work P z width a
  have field : f.market.failures.effective.work ≤ f.market.failures.test.work := by
    simp only [FailureWords.test,Expr.work]; omega
  have density : GlobalTests.kinds N k ≤ v.testVoteFactor := by
    rw [show N=publicStages v.W from fixed_stage_count z v.W]
    unfold testVoteFactor
    omega
  have rows : GlobalTests.rows z N k ≤ v.testVoteFactor*2^z := by
    rw [GlobalTests.rowCount]
    exact Nat.mul_le_mul_right _ density
  refine ⟨shape.1.trans_le word,shape.2.1.trans_le word,?_,shape.2.2.1.trans_le rows,shape.2.2.2.trans_le rows,?_⟩
  · change f.market.failures.effective.work ≤ v.testVoteFactor
    exact (field.trans fail).trans (by unfold testVoteFactor; omega)
  · change f.market.failures.rows ≤ v.testVoteFactor*2^z
    rw [v.discrepancy_scan_rows P z width a]
    exact Nat.mul_le_mul_right _ (by unfold testVoteFactor; omega)

/-- The actual policy run by the private RAM reads the same three tests. -/
theorem native_test_vote_bounds (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks)
    (src tab dst : ℕ) (owners : Bank) (a : Attempt) :
    TestVoteBounds v.testVoteFactor z (repair (v.nativeChart P z width r banks src tab dst owners) a).tests := by
  have raw := v.test_vote_bounds P z width a
  exact ⟨raw.excessWork,raw.payloadWork,raw.discrepancyWork,raw.excessRows,raw.payloadRows,raw.discrepancyRows⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
