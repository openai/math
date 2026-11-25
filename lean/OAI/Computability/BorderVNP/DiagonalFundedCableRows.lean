import OAI.Computability.BorderVNP.DiagonalExternalFragmentCables

/-! # Recorded cable rows at the original edge indices -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments
open Crossing Packing RoutingISA Packing.RoutingOutputs

/-- A return recorded at the equal-sized hardware cable rectangle certifies the same
cable rows at the original sparse edge embedding. -/
theorem CableRows.beforeCableCast {D C ne cables n : ℕ} {P : Type*} [Fintype P]
    {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Fin C)
    (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin n) (host : BorderVNP.Cube.HostScatter.Layout)
    (mem : ℕ → ℕ) (he : ne = cables)
    (observed : CableRows N cell (edge.trans (finCongr he).toEmbedding) port host mem) :
    CableRows N cell edge port host mem := by
  cases he
  exact observed

open Lean Meta Elab Term in
/-- Read the actual returned cable-row assertion and undo just its final equality
cast of the sparse edge embedding. -/
elab "originalFundedCableRows%" observedTerm:term:max : term => do
  let proof ← elabTerm observedTerm none
  let some source ← whnfUntil (← inferType proof) ``CableRows
    | throwError "expected the returned cable-row assertion"
  let #[dim,cells,cables,ports,P,enum,bits,network,cell,edgeAt,port,host,mem] := source.getAppArgs
    | throwError "unexpected cable-row operands"
  let some joined ← whnfUntil edgeAt ``Function.Embedding.trans
    | throwError "expected the original sparse edge followed by its finite cast"
  let edge := joined.getAppArgs[joined.getAppNumArgs-2]!
  let cast := joined.getAppArgs.back!
  let some embeds ← whnfUntil cast ``Equiv.toEmbedding
    | throwError "expected the finite index equivalence"
  let some adjusted ← whnfUntil embeds.getAppArgs.back! ``finCongr
    | throwError "expected the original cable count equality"
  let #[num,_,he] := adjusted.getAppArgs | throwError "unexpected finite cast operands"
  return mkAppN (Lean.mkConst ``CableRows.beforeCableCast source.getAppFn.constLevels!)
    #[dim,cells,num,cables,ports,P,enum,bits,network,cell,edge,port,host,mem,he,proof]

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
