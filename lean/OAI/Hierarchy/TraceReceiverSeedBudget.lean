import OAI.Hierarchy.TraceReceiverSeedDimensions
import OAI.Hierarchy.TraceReceiverSeedPrice
import OAI.ThreeFlat.Diagonal.PhysicalWordAssembly

namespace OAI
/-! # The archived work seed for every native input bit and initial cursor tree -/

noncomputable section
namespace Hierarchy.TraceReceiverSeedWords

open ThreeFlat Diagonal Diagonal.LaneCursor Diagonal.HistoryContraction
open Diagonal.TraceSourceOwner Diagonal.CompressorPacking
open Computability.VPVNP Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open scoped Classical BigOperators
open private budgetGrid budgetShape from OAI.Hierarchy.TraceReceiverSeedDimensions

variable {F : Type} [Field F] [Fintype F] {k low W pc regs words S base fuel : ℕ}
  (M : Machine W pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
  (hF : Fintype.card F ≤ 2^W) (st : Word W) (B : PhysicalStage.Block F) (hk : 2≤k+1)
theorem words_ordered : (budgetState M t hF st B hk).OrderedHalves (wordsLayout M t hF st B hk) := by
  refine ⟨fun _ => rfl,?_⟩
  intro v i
  exact congrArg Prod.fst (Native.ShrinkStage.Halves.portOrder_value (budgetState M t hF st B hk).graph (budgetState M t hF st B hk).chart v i)

theorem seed_budget (v : PairedCursor.Site (k+1)) :
    1+(budgetState M t hF st B hk).incidentWidth v ≤ start M t hF st B hk v ∧
    (wordsLayout M t hF st B hk).ports.form.width v ≤ 2*start M t hF st B hk v ∧
    (forest M t hF st B hk v).resources ≤ start M t hF st B hk v := by
  let fee := TraceBitHeader.seedTraceWork low (budgetShape M t hF st).stride
    (budgetGrid M t hF st).cells B.cursorCopies ((k+1)+low)
  have billed := billed_resources M t hF st B hk v
  have halves := (words_ordered M t hF st B hk).halfBits_eq_incident v
  rw [halves] at billed
  change (forest M t hF st B hk v).resources ≤ 1+(budgetState M t hF st B hk).incidentWidth v+
    (if v.1=0 then fee else 0) at billed
  have payload := seed_pairs_budget M t hF st B hk v
  have n : width M t hF st v ≤ 2*pairs M t hF st v := by unfold pairs; omega
  refine ⟨by omega,?_,?_⟩
  · change width M t hF st v+(wordsLayout M t hF st B hk).ports.halfBits v ≤ _
    rw [halves]
    omega
  · apply billed.trans
    change 1+(budgetState M t hF st B hk).incidentWidth v+(if v.1=0 then fee else 0) ≤
      1+((budgetState M t hF st B hk).incidentWidth v+
        (if decide (v.1=0) then pairs M t hF st v+fee else 0))
    by_cases first : v.1=0 <;>
      simp only [first,decide_true,decide_false,Bool.false_eq_true,ite_false,ite_true] <;> omega

end Hierarchy.TraceReceiverSeedWords

end
end OAI
