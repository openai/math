import OAI.ThreeFlat.RAM.TickExecutionInputs
import OAI.ThreeFlat.Diagonal.TickSlotForest
import OAI.ThreeFlat.Diagonal.TickTeamTransfer

namespace OAI
/-! # Team products of the actual native transfer weights -/

noncomputable section
namespace ThreeFlat.RAM.TickActiveROM
open Contraction Diagonal.TickChronology Diagonal.TickSlotForest Diagonal.TickTeamTransfer
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] {p H J w : ℕ} {B : Layout} {clock : Clock}
    {fit : Fits (TickWeightedBank.shape F p H J) w}

def CellInput.checked (x : CellInput B clock fit) (ph : Phase) (oa na oc nc : Fin B.bits → Bool) : Prop :=
  x.aux.accepts ph true oa na ∧ if ph=.scan then TickChunkCheck.valid true
    (TickGroupScanBank.layout B.scan x.lo x.group) x.intervals x.before x.after
    (chunkView B x.lo x.group oc) (chunkView B x.lo x.group nc) else oc=nc

theorem CellInput.weight_guard (x : CellInput B clock fit) (ph : Phase) (oa na oc nc : Fin B.bits → Bool)
    (pin : Fin p → Bool) : x.weight ph oa na oc nc pin =
      if x.checked ph oa na oc nc then (if ph=.evaluate then x.net.eval pin else 1) else 0 := by
  unfold CellInput.weight CellInput.checked
  by_cases h : x.aux.accepts ph true oa na
  · cases ph <;> simp [h]
  · simp [h]

theorem CellInput.weight_forest (x : CellInput B clock fit) (ph : Phase) (oa na oc nc : Fin B.bits → Bool)
    (pin : Fin p → Bool) {n : ℕ} (nodes : Fin n → BitNetwork F p) (extra unit : ℕ)
    (compiled : x.net = Diagonal.TraceCircuit.addPadding (network nodes) extra unit) :
    x.weight ph oa na oc nc pin =
      if x.checked ph oa na oc nc then (if ph=.evaluate then ∏ i, (nodes i).eval pin else 1) else 0 := by
  rw [x.weight_guard,compiled,Diagonal.TraceCircuit.addPadding_eval,Diagonal.TickSlotForest.eval]

/-- Each team reads the same raw proposal. Its selected cell forest is the
only team-specific weight in the product. -/
theorem team_product {q : ℕ} (pos : 0 < q) (x : Fin q → CellInput B clock fit) (ph : Phase)
    (oa na oc nc : Fin B.bits → Bool) (pin : Fin q → Fin p → Bool)
    (guard : Prop) (common : ∀ j, (x j).checked ph oa na oc nc ↔ guard) :
    (∏ j, (x j).weight ph oa na oc nc (pin j)) =
      if guard then (if ph=.evaluate then ∏ j, (x j).net.eval (pin j) else 1) else 0 := by
  simp_rw [CellInput.weight_guard,common]
  rw [repeated_guard pos]
  by_cases h : ph=.evaluate <;> simp [h]


end ThreeFlat.RAM.TickActiveROM

end
end OAI
