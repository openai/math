import OAI.Hierarchy.TraceAdmittedFactor
import OAI.ThreeFlat.Diagonal.TraceFactorPins
import OAI.Hierarchy.TracePhysicalTileCaps
import OAI.Hierarchy.TraceReceiverSeedBudget
import OAI.ThreeFlat.Diagonal.PhysicalProgramAssembly

namespace OAI
/-! # Pin room of a terminal factor in its registered physical archive -/

noncomputable section
namespace Hierarchy.TraceDistribution.Physical
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open Filter Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Topology

variable {F : Type} [Field F] [Fintype F] (B : Block F)

/-- Transport the original repeated program's compiler and charge scan across
the lane equality used by the physical trace. -/
def registerOnLanes (Pins : Type) (n rem : ℕ) {lanes : ℕ} (X : State (2^(B.exponent 0)) lanes)
    (e : lanes=(B.repeat n).charge+rem) :
    let R := Program.recast e X ((B.repeat n).run rem (e ▸ X))
    R.Assembler Pins × R.Charges := by
  subst lanes
  exact ⟨(B.repeat n).assembly rem X, B.charges n rem X⟩

omit [Fintype F] in
theorem registered_local_floor (Pins : Type) (n rem : ℕ) {lanes : ℕ}
    (X : State (2^(B.exponent 0)) lanes) (e : lanes=(B.repeat n).charge+rem) :
    let R := Program.recast e X ((B.repeat n).run rem (e ▸ X))
    R.LocalFloor (registerOnLanes B Pins n rem X e).2 := by
  subst lanes
  exact (B.repeat n).certified_floor _ (B.factor_bound n) rem X

omit [Fintype F] in
private theorem archive_tariff_two (w depth setup maps stages : ℕ) :
    2 ≤ FactorWork.archiveTariff w depth setup maps stages B.localCoefficient := by
  unfold FactorWork.archiveTariff
  exact (fresh_price_scale B w).trans
    ((Nat.le_mul_of_pos_left _ (by positivity : 0 < 2*stages+1)).trans
      (Nat.le_mul_of_pos_left _ (by positivity : 0 < 10025+1016*depth+setup+maps)))

/-- The pin-room premise of the contraction evaluator follows from the same
archive word bound already used to run the selected factor. -/
theorem native_factor_pins {w k low pc regs words S base fuel : ℕ}
    (M : Machine (64*w) pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F ≤ 2^(64*w)) (st : Word (64*w)) (hk : 2≤k+1)
    (n rem : ℕ) (e : k+1=(B.repeat n).charge+rem) :
    let d := (k+1)+low
    let grid := TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words d
    let X := B.cursorState hk low (1+(d+d)) grid.cells
    let R := Program.recast e X ((B.repeat n).run rem (e ▸ X))
    let reg := registerOnLanes B (Fin S → Bool) n rem X e
    let L := TraceReceiverSeedWords.wordsLayout M t hF st B hk
    let N := TraceReceiverSeedWords.forest M t hF st B hk
    let start := TraceReceiverSeedWords.start M t hF st B hk
    ∀ (h : R.plan.History) (depth setup maps W : ℕ) (v : (R.plan.finish h).Site),
      let unit := FactorWork.archiveTariff w depth setup maps (B.repeat n).length B.localCoefficient
      publishedWork R h reg.2 start unit v ≤ 2^W →
        (R.plan.assemble h (R.wordAssembly reg.1.steps L) N).1.width v ≤ 2^W := by
  intro d grid X R reg L N start h depth setup maps W v unit room
  apply R.assembled_pins_fit h reg.1.steps reg.2 (registered_local_floor B _ n rem X e)
    L N start (fun x => (TraceReceiverSeedWords.seed_budget M t hF st B hk x).2.1) v
    (archive_tariff_two B w depth setup maps (B.repeat n).length)
  exact room


end Hierarchy.TraceDistribution.Physical

end
end OAI
