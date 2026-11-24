import OAI.Computability.VPVNP.PairSelectedPacketGeometry
import OAI.Computability.VPVNP.PairSelectedRowShape
import OAI.Computability.VPVNP.PairVertexSelectedControl

/-! # The common descendant count for all calls on a selected branch -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open Compression NetworkKernel LocalHistory DFS NodeArguments TraversalRows
open private root_address from OAI.Computability.VPVNP.PairVertexSelectedControl

variable {k K : Type*} [Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (κ : B.Entry → K) (hκ : B.IsSolution κ) {lanes : ℕ}
    (T : ℕ) (hT : T*S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute κ hκ T hT X).Choices) (rowBase : ℕ)

/-- The descendant addresses are determined by the selected row pointers. -/
noncomputable def selectedDesc : ℕ → List ℕ :=
  (selected_descendants B κ hκ T hT X z rowBase).choose

theorem selectedDesc_leaf (v : X.network.Site) :
    selectedDesc B κ hκ T hT X z rowBase (sitePointers B.recordLimit rowBase (siteOrder X) v).1 = [] :=
  (selected_descendants B κ hκ T hT X z rowBase).choose_spec.1 v

theorem selectedDesc_level :
    let passes := CompressorRecords.executeLevels B κ hκ T hT X z
    let pos := TraversalRoles.layerBase B.recordLimit rowBase (TraversalRoles.selected B κ hκ T hT X z)
    ∀ i : Fin passes.length, LevelShape B κ hκ (selectedDesc B κ hκ T hT X z rowBase)
      B.recordLimit (pos i.val) (pos (i.val+1)) passes[i] :=
  selected_rowShape B κ hκ (selectedDesc B κ hκ T hT X z rowBase) T hT X z rowBase
    (selected_descendants B κ hκ T hT X z rowBase).choose_spec.2.1

theorem selectedDesc_root :
    let Y := (B.execute κ hκ T hT X).finalState z
    let trees := selectedTrees B κ hκ T hT X z rowBase
    ∀ (v : Y.network.Site) (h : Y.network.Half v), subtreeAddresses (selectedDesc B κ hκ T hT X z rowBase)
      ⟨(trees v).address,packed Y v h⟩ = (trees v).preorder := by
  intro Y trees v h
  let c := (B.execute κ hκ T hT X).termChain (B.records κ hκ T hT X) z
  let r := selectedParsers B κ hκ T hT X z
  let ptr := selectedPointers B κ hκ T hT X z rowBase
  let leaf := sitePointers B.recordLimit rowBase (siteOrder X)
  have eqn : (trees v).address = lastRowAddresses c ptr (fun u => (leaf u).1) v :=
    root_address c r ptr (fun u => leafTree (leaf u)) v
  change (trees v).address :: selectedDesc B κ hκ T hT X z rowBase (trees v).address = _
  rw [eqn]
  exact ((selected_descendants B κ hκ T hT X z rowBase).choose_spec.2.2 v).1.symm

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
