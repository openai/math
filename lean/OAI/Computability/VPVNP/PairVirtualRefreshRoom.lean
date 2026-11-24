import OAI.Computability.VPVNP.PairRefreshSelectedRoom
import OAI.Computability.VPVNP.PairVirtualRootBudget

/-! # Capacity of all chronological refresh rows in the virtual pair -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression
open CompressorRecords CursorNetwork CursorBounds Filter LocalHistory TraversalRows TraversalRoles

variable {k : Type} [_root_.Field k] {S : BlockSchedule k}
    (D : FixedProgramDiagonal.Program) (B : S.Templates) (u : PairExponents B.growthConstant)

attribute [local irreducible] BlockSchedule.Templates.execute BlockProgram.layout
  CursorNetwork.cursorState

/-- The same private capacity threshold applies to the true scan state and
the public workspace of every nomination and every compressor branch. -/
theorem eventually_virtualRefreshRooms (labels : ℕ) (haddr : max S.laneBits 5 ≤ D.addressFactor)
    (hnum : D.numerator = (liveRatio u).num) (hden : D.denominator = (liveRatio u).den) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn D.constants.circuitExponent)
      (ht : 21 ≤ 2 ^ (D.geometry n).w) (clock : 44 ≤ n ^ 10000)
      (A : Type) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
      let G := D.executionGroup n ht clock
      let X := V.scanState
      let T := blockCount (u.θ : ℝ) n
      ∀ z : (B.execute f hf T le_rfl X).Choices,
        RefreshHook.SelectedRows.Rooms n labels G.w (terminalOperands G 2).val X.positions T
          ⟨leafLayer (siteOrder X), .cursor⟩ (executeLevels B f hf T le_rfl X z) := by
  let start n := (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n)
  have poly : PolynomiallyBounded start := by
    have eqn : start = fun n => (LiveProgram.Layout.pairWorkspace D.constants).eval
        (paperGeometry D.addressFactor (liveCapacity u) n) := by
      funext n
      exact congrArg (PublicExpr.eval · (LiveProgram.Layout.pairWorkspace D.constants))
        (paperGeometry_eq D B u hnum hden n)
    rw [eqn]
    exact CompressedPair.startup_workspace_polynomial _ D.address_pos (liveCapacity_polynomial u)
  filter_upwards [RefreshHook.SelectedRows.eventually_rooms B u D.addressFactor haddr poly labels,
    CompressedPair.eventually_startup_inputs D.constants D.address_pos (liveCapacity_polynomial u)]
    with n room inputs
  intro hn V ht clock A _ f hf
  dsimp only
  rw [V.scanState_pairInput]
  let G := D.executionGroup n ht clock
  have ports := inputs (CounterPublic.actualPrefix D.literal)
  rw [← paperGeometry_eq D B u hnum hden n] at ports
  have startEq : (terminalOperands G 2).val = start n := ports.1
  rw [startEq, pairInput_positions]
  exact room (laneLabels _ _ V.lanes) V.dimension le_rfl A f hf

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
