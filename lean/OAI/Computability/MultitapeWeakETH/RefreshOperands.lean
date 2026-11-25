import OAI.Computability.MultitapeWeakETH.OperandSpan
import OAI.Computability.VPVNP.CompressorRefreshPayloadHistory
import OAI.Computability.VPVNP.CompressorRefreshMapFrameFields

/-! # Refresh operand addresses with child and parent on distinct tapes -/

namespace OAI.Computability.MultitapeWeakETH.RefreshOperands

open VPVNP BurstRAM Compression Compression.Refresh Compression.DegreeRefresh CompressorRecords
open PortRefresh OperandInputs PhaseRecipe NewSlots PairSimulation.NodeArguments
open DescriptorSpace
open private addr_val from OAI.Computability.VPVNP.CompressorRefreshTraversalHeaders
open scoped Fin.CommRing
noncomputable section

private def placement : Traversal := ⟨.lit 0,.lit 0,.lit 0,.lit 0,.publicWord 0,.header 58⟩

/-- Each private bit packet starts at offset zero. The old and new inverse/width
columns still occupy their published native addresses. -/
def input (s : LevelRecipe.Shape) : Input :=
  let I := fromLevel s TraversalHeaders.level placement
  { I with parent := { I.parent with actualIn := TraversalHeaders.current 58, width := TraversalHeaders.current 59 } }

variable {w g : ℕ} (s : LevelRecipe.Shape) (X : State s.a (s.a+g))
  (p : (X.Base × BitWord g) × Fin (2^s.a)) (P : SlotGraph (Fin (2^s.a)) s.dH)
  (hD : 1 < 2^s.a) (hd : s.dH+1 ≤ 2^s.a₀)
  (internal : X.Base × BitWord g → Fin (2^s.a) × Fin s.dH → ℕ)
  (T U : IncidenceDirectory w) (C : LevelRecipe.Context w)

/-- The expressions use the old header, next header and site ordinal from the
caller's public context. The private operand addresses index the two bit packets. -/
theorem describes {oldHead newHead start : ℕ} {A : Arena}
    (G : TraversalHeaders.Geometry (Fintype.card X.Base) g oldHead newHead start A T U C.memory)
    (state : C.state.val = oldHead) (succ : (C.pub 2).val = newHead)
    (site : (C.pub 0).val = (sites X.baseIndex (bitWordFinEquiv g) p).val) (lanes : 2^g < 2^w) :
    let plan := Allocation.plan X s.a₀ s.dH s.ties s.stride start
    Describes (input s) C.pub C.state C.memory X p P hD hd internal ⟨0,0⟩ 0 0 T U
      (plan.scratch w) (word plan.demand) (word plan.term) := by
  dsimp only
  have oldRead (j : ℕ) (hj : j ≤ 60) : C.eval (.header j) = C.memory (oldHead+j) :=
    congrArg C.memory (addr_val state ((Nat.add_le_add_left hj _).trans_lt G.oldRoom))
  have newRead (j : ℕ) (hj : j ≤ 59) : C.eval (TraversalHeaders.current j) = C.memory (newHead+j) :=
    congrArg C.memory (addr_val succ ((Nat.add_le_add_left hj _).trans_lt G.newRoom))
  have level : LevelRecipe.Describes (s:=s) TraversalHeaders.level C X start T :=
    ⟨(oldRead 60 le_rfl).trans G.scratch,(oldRead 0 (by decide)).trans G.vertices,
     (oldRead 3 (by decide)).trans G.residual,(oldRead 54 (by decide)).trans (G.oldIncidence 0),
     (oldRead 56 (by decide)).trans (G.oldIncidence 2),(oldRead 59 (by decide)).trans (G.oldIncidence 5)⟩
  have prev := describes_fromLevel s TraversalHeaders.level placement C X p P
    hD hd internal ⟨0,0⟩ 0 0 start T level rfl rfl rfl rfl site
    ((oldRead 58 (by decide)).trans (G.oldIncidence 4)) lanes
  refine ⟨prev.childRep,?_,prev.site,prev.lanes,prev.offOut,prev.offIn,prev.widthOut,prev.widthIn,
    prev.demandBase,prev.termBase⟩
  exact ⟨prev.parentRep.arena,prev.parentRep.stride,prev.parentRep.node,prev.parentRep.site,
    (newRead 58 (by decide)).trans (G.newIncidence 4),(newRead 59 le_rfl).trans (G.newIncidence 5)⟩

end
end OAI.Computability.MultitapeWeakETH.RefreshOperands
