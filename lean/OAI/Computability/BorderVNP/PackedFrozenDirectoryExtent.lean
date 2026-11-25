import OAI.Computability.BorderVNP.PackedFrozenPacketDirectories

/-! # Extent of the five directory fields in the signed geometry output -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open CellPacketGeometry LiveWords Packing.RoutingOutputs Retained

/-- The descriptor-bank base, its two size fields, and both appended bundle
bank bases fit within the output extent of the frozen packet. -/
theorem frozenPacketDirectories_extent {E I Orig : Type} {slots cells : ℕ}
    (tpl : Template E I Orig slots (cells+1)) (origin cables originals live bundleBits : ℕ) :
    let dirs := frozenPacketDirectories tpl origin cables originals live bundleBits
    let outputs := TerminalCells.signedGridOutputCount cables cells originals live 37
      (Total tpl.publicDepth tpl.chunkDepth)+(2^bundleBits+2^bundleBits)
    dirs.sorted ≤ origin+outputs ∧ dirs.padded ≤ origin+outputs ∧
      dirs.stops ≤ origin+outputs ∧ dirs.bundlePayload ≤ origin+outputs ∧ dirs.bundleInverse ≤ origin+outputs := by
  dsimp only
  obtain ⟨sorted,padded,stops,payload,inverse⟩ := frozenPacketDirectories_locations tpl origin cables originals live bundleBits
  have packet : packetBase origin cables cells originals live 37+Total tpl.publicDepth tpl.chunkDepth =
      origin+TerminalCells.signedGridOutputCount cables cells originals live 37 (Total tpl.publicDepth tpl.chunkDepth) := payload
  have marker : cells+1+3*tpl.chunkLabels.length ≤ 2^tpl.chunkDepth :=
    (Nat.le_add_right _ (cells+1)).trans (Nat.le_pow_clog (by decide : 1 < 2) _)
  rw [sorted,padded,stops,payload,inverse]
  let ordinary := TerminalCells.signedGridOutputCount cables cells originals live 37 (Total tpl.publicDepth tpl.chunkDepth)
  have extend : origin+ordinary ≤ origin+(ordinary+(2^bundleBits+2^bundleBits)) :=
    Nat.add_le_add_left (Nat.le_add_right _ _) _
  have prim : descriptorBank (packetBase origin cables cells originals live 37) tpl.publicDepth ≤ origin+ordinary := by
    rw [←packet]
    exact Nat.add_le_add_left (Nat.le_add_right _ _) _
  have pad : 2^tpl.chunkDepth ≤ origin+ordinary := by
    rw [←packet]
    exact (Nat.le_add_right _ _).trans ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _))
  refine ⟨prim.trans extend,pad.trans extend,(marker.trans pad).trans extend,extend,?_⟩
  rw [Nat.add_assoc]
  exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.le_add_right _ _) _) _

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
