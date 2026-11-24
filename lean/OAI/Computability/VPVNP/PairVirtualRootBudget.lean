import OAI.Computability.VPVNP.FixedProgramOperandFits
import OAI.Computability.VPVNP.LiveCertificateAssembly
import OAI.Computability.VPVNP.LiveVirtualPairCursorBoundary
import OAI.Computability.VPVNP.PairTerminalVertexPackedThreshold
import OAI.Computability.VPVNP.PairTerminalPackedBudget
import OAI.Computability.VPVNP.LiveCompressedPairStartupInputs
import OAI.Computability.VPVNP.PairNativeGeometry

/-!
# The physical root bounds before the selected branch

One length threshold gives the terminal workspace, private cache fit and
maximum field width for all branches of the actual virtual pair. The
workspace has the tight chronological level count emitted by the calendar.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression
open CompressorRecords DescriptorSpace CursorNetwork CursorBounds Filter

variable {K : Type*} [_root_.Field K] {S : BlockSchedule K} (D : FixedProgramDiagonal.Program)
  (B : S.Templates) (u : PairExponents B.growthConstant)

/-- Public terminal slots six and nine carry the input length and the fixed motif count.
The two values fit without word reduction beyond one threshold, uniformly over groups. -/
theorem eventually_terminalOperandSizes {labels : ℕ} (hlabels : D.constants.motifLabels = labels) :
    ∀ᶠ n : ℕ in atTop, ∀ (ht : 21 ≤ 2 ^ (D.geometry n).w) (clk : 44 ≤ n ^ 10000),
      let G := D.executionGroup n ht clk
      (terminalOperands G 6).val = n ∧ (terminalOperands G 9).val = labels := by
  filter_upwards [CompressorRecords.CursorRAM.eventual_word_room D.addressFactor D.address_pos
    PolynomiallyBounded.id, CompressorRecords.CursorRAM.eventual_word_room D.addressFactor D.address_pos
    (PolynomiallyBounded.const D.constants.motifLabels)] with n length count
  intro ht clk G
  exact ⟨Nat.mod_eq_of_lt length, (Nat.mod_eq_of_lt count).trans hlabels⟩

attribute [local irreducible] BlockSchedule.Templates.execute BlockProgram.layout CursorNetwork.cursorState

set_option maxHeartbeats 800000 in
theorem eventually_selectedRootBudget (haddr : max S.laneBits 5 ≤ D.addressFactor)
    (hnum : D.numerator = (liveRatio u).num) (hden : D.denominator = (liveRatio u).den) (C : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn C) (ht : 21 ≤ 2^(D.geometry n).w)
      (hf : 44 ≤ n^10000) (A : Type*) [CommRing A] (f : B.Entry → A) (ok : B.IsSolution f),
      let G := D.executionGroup n ht hf
      let X := V.scanState
      let T := blockCount (u.θ : ℝ) n
      let E := B.execute f ok T le_rfl X
      let L := BlockProgram.layout B (terminalOperands G 2).val X.positions T
      3 ≤ n ∧ PairNativeGeometry.Fits D.numerator D.denominator n (D.geometry n).w ∧
        (terminalOperands G 6).val = n ∧ ∀ z : E.Choices,
          let Y := E.finalState z
          let ls := TraversalRows.selectedLayers B f ok T le_rfl X z
          let tags := TraversalRoles.selected B f ok T le_rfl X z
          VertexPacked G L B.recordLimit tags Y.totalWidth ∧ Y.maxWireWidth ≤ n ∧
            (TerminalLayout.privateRegions (slotDegree S) n (endAddress L+TraversalRows.words B.recordLimit ls)
              (Fintype.card B.Entry)).stackBase < 2^(D.geometry n).w := by
  let start := fun n => (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n)
  have poly : PolynomiallyBounded start := by
    have eqn : start = fun n => (LiveProgram.Layout.pairWorkspace D.constants).eval
        (paperGeometry D.addressFactor (liveCapacity u) n) := by
      funext n
      change (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n) = _
      rw [paperGeometry_eq D B u hnum hden n]
    rw [eqn]
    exact CompressedPair.startup_workspace_polynomial _ D.address_pos (liveCapacity_polynomial u)
  filter_upwards [eventually_ge_atTop 3,
    PairNativeGeometry.eventually_fits D.numerator D.denominator D.addressFactor D.address_pos,
    CompressedPair.eventually_startup_inputs D.constants D.address_pos (liveCapacity_polynomial u),
    eventually_vertexPacked B u D.addressFactor haddr poly,
    TerminalLayout.eventually_packedFit B u D.addressFactor haddr poly 0 (fun _ => 0) (PolynomiallyBounded.const 0),
    eventually_pairBranchBounds B u D.addressFactor haddr] with n hn₃ hgeo hwords hpack hstack hbranch
  intro hn V ht hf A inst f ok
  dsimp only
  rw [V.scanState_pairInput]
  let G := D.executionGroup n ht hf
  let coords := laneLabels _ _ V.lanes
  have words := hwords (CounterPublic.actualPrefix D.literal)
  rw [←paperGeometry_eq D B u hnum hden n] at words
  have length : (terminalOperands G 6).val = n := words.2.1
  have exp : (terminalOperands G 7).val = addressBits D.addressFactor n := words.2.2.1
  have workspace : (terminalOperands G 2).val = start n := words.1
  refine ⟨hn₃,hgeo,length,?_⟩
  intro z
  have pack := hpack G rfl rfl exp coords V.dimension le_rfl A f ok z
  have s := hstack coords V.dimension le_rfl A f ok z
  have bound := hbranch.2.2 coords V.dimension le_rfl A f ok z
  have hpow {x : ℝ} (h : x ≤ 1) : (n : ℝ)^x ≤ n := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) h
  have width := Nat.cast_le.mp ((Nat.cast_le.mpr bound.2.2.2.2.1).trans (bound.2.2.2.2.2.1.trans (hpow (by norm_num))))
  change VertexPacked G (BlockProgram.layout B (terminalOperands G 2).val _ _) _ _ _ ∧ _ ∧ _
  rw [workspace]
  refine ⟨pack,width,?_⟩
  rw [pairInput_positions]
  have h := s.2.2.2.1
  simp only [Nat.zero_mul,Nat.add_zero] at h
  exact h

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
