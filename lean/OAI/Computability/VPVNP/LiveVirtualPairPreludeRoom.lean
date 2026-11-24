import OAI.Computability.VPVNP.PairTerminalPreludeBudget
import OAI.Computability.VPVNP.LiveVirtualPairCanonicalScan
import OAI.Computability.VPVNP.LiveVirtualPairCursorBoundary
import OAI.Computability.VPVNP.LiveCompressedPairPaperStartup
import OAI.Computability.VPVNP.FixedProgramOperandFits

/-! # Public words and room of the selected terminal prelude -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLayout

open BurstRAM LiveProgram CompressorRecords DescriptorSpace

/-- Bounds shared by the actual bootstrap, wire scan and traversal stages
at one selected branch. The workspace and address exponent are the words
the program reads. -/
structure PreludeRoom {w : ℕ} (pub : Fin 11 → Word w) (L : Layout)
    (r cap limit positions rows tags width arcs : ℕ) : Prop where
  workspace : (pub 2).val = L.base
  tag : (PairTag.address pub).val < (pub 2).val+6
  exponent : (pub 7).val = r
  exponentFit : r < w
  reserve : 32 ≤ L.base+2^r*2^r
  room : L.base+2^r*2^r ≤ 2^w
  below : endAddress L+2*rows+width ≤ TerminalBootstrap.address L.base r
  ordinal : 2*tags*(positions+1) < 2^w
  slots : arcs ≤ slotCapacity L
  cells : arcs ≤ tableWords L
  totalFit : width < 2^w
  bootClock : TerminalBootstrap.cost L.shape limit+1+30 ≤ cap
  widthClock : 60 ≤ cap
  rowClock : TraversalController.callFuel limit+30 ≤ cap

end PairSimulation.TerminalLayout

namespace FixedProgramDiagonal.Program

open Compression CursorBounds CursorNetwork BurstRAM LiveProgram CompressedPair LabelEvaluator CompressorRecords
open PairStages.Group.CompressedPaths PairSimulation LocalHistory TraversalRows TraversalRoles TerminalPrefix Filter

variable {K : Type} [_root_.Field K] {S : BlockSchedule K}

set_option exponentiation.threshold 10000 in
/-- Uniform terminal room on the actual eleven words and finite-model
selection. All stage witnesses use this same runtime layout and clock. -/
theorem eventually_paperDescriptorRoom (D : FixedProgramDiagonal.Program) (B : S.Templates)
    (u : PairExponents B.growthConstant) (C : ℕ) (hb : max S.laneBits 5 ≤ D.addressFactor)
    (num : D.numerator = (liveRatio u).num) (den : D.denominator = (liveRatio u).den) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn C)
      (ht : 21 ≤ 2^(D.geometry n).w) (hc : 44 ≤ n^10000) {p : Nat.Primes}
      (M : Model p (B.compressorDegree n) (B.compressorEquations hn C)) (z : (V.selection (M := M)).Choices),
      let G := D.executionGroup n ht hc
      let pub := publicWords G
      let κ := B.compressorValues hn M
      let ok := B.compressorValues_solution hn M
      let T := blockCount (u.θ : ℝ) n
      let base := (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n)
      let L := BlockProgram.layout B base (initialPositions D.addressFactor n) T
      let Y := (V.selection (M := M)).finalState z
      let ls := selectedLayers B κ ok T le_rfl V.scanState z
      let tags := selected B κ ok T le_rfl V.scanState z
      TerminalLayout.PreludeRoom pub L (addressBits D.addressFactor n) (clockAt pub (fuel G) Stage.terminal)
        B.recordLimit V.scanState.positions (words B.recordLimit ls) tags.length Y.totalWidth (arcCount Y) := by
  let start n := (LiveProgram.Layout.pairWorkspace D.constants).eval (paperGeometry D.addressFactor (liveCapacity u) n)
  have poly : PolynomiallyBounded start := startup_workspace_polynomial D.constants D.address_pos (liveCapacity_polynomial u)
  filter_upwards [TerminalLayout.eventually_preludeRoom B u D.addressFactor hb poly,
    eventually_startup_inputs D.constants D.address_pos (liveCapacity_polynomial u)] with n fits inputs
  intro hn V ht hc p M z G pub κ ok T base L Y ls tags
  have geom := paperGeometry_eq D B u num den n
  obtain ⟨baseWord,_,exp,tag⟩ := inputs G.lit
  rw [← geom] at baseWord exp tag
  change (pub 2).val = base at baseWord
  change (pub 7).val = addressBits D.addressFactor n at exp
  change (PairTag.address pub).val < (pub 2).val at tag
  have cut := fits (laneLabels _ _ V.lanes) V.dimension le_rfl M.algebra κ ok
  dsimp only at cut
  rw [← V.scanState_pairInput] at cut
  have positions : V.scanState.positions = initialPositions D.addressFactor n := by
    rw [V.scanState_pairInput]; exact pairInput_positions S _ _
  have offset : start n = base := by unfold start; rw [← geom]
  have bounds := cut z G le_rfl
  rw [offset] at bounds
  obtain ⟨hr,reserve,room,below,ord,slots,cells,totalFit,clock₀,clock₁,clock₂⟩ := bounds
  rw [positions] at reserve room below slots cells clock₀
  exact ⟨baseWord,tag.trans_le (Nat.le_add_right _ _),exp,hr,reserve,room,below,ord,slots,cells,totalFit,
    clock₀,clock₁,clock₂⟩

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
