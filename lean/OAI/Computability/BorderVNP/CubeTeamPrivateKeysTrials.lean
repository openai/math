import OAI.Computability.BorderVNP.CubeScatterPacketPrepared
import OAI.Computability.BorderVNP.CubeScatterSinglePrepared
import OAI.Computability.BorderVNP.CubeISAOwnedSingleTape

/-! # Private choices in the order of the native packet and singleton trials

Each accepted packet contributes the choices from its body slots. An accepted
singleton contributes its bits when the two symbols at the grouping coordinate
coincide. Rejected trials contribute the empty list to both native scans.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open Physical Physical.Owned RoutingISA.Owned

/-- The packet row consumes the private digits of each visited body in trial order. -/
theorem PacketRowData.rowChoices_eq_visits {n d blocks b h K s : ℕ}
    (D : PacketRowData n d blocks b h K s) :
    rowChoices packetTrialValid D.choices = (packetVisits blocks D.axis D.pair).flatMap
      fun p => ((D.body p).map Position.digit).flatMap Digit.choices := by
  rw [← D.all_words, rowChoices, List.ofFn_eq_map, ← List.flatMap_def]
  apply List.flatMap_congr
  intro t _
  by_cases ok : packetTrialValid t <;>
    simp [PacketRowData.choices, PacketRowData.trialWords, packetTrial, ok, PacketRowData.packet]

/-- A diagonal row consumes every visited singleton bit in slot order. A strict
row reads its singleton bits from the shared stream and consumes no private choices. -/
theorem SingleRowData.rowChoices_eq_visits {n d blocks width : ℕ}
    (D : SingleRowData n d (blocks * width)) :
    rowChoices D.selected D.localBits = if D.left = D.right then
      (singleVisits blocks width D.axis D.left D.right).map D.slotBit else [] := by
  by_cases diag : D.left = D.right
  · rw [ite_eq_left diag, singleVisits, List.map_flatMap, rowChoices, List.ofFn_eq_map,
      ← List.flatMap_def]
    apply List.flatMap_congr
    intro t _
    rw [D.localBits_eq, ite_eq_left diag, D.candidate_bits]
  · simp [rowChoices, D.localBits_eq, diag]

end Cube.Scatter

end BorderVNP
end Computability
end OAI
