import OAI.Hierarchy.TraceReceiverChargePrice
import OAI.Hierarchy.TraceReceiverVisitArithmetic

namespace OAI
/-! # Joint pricing of the issued tree, chronological visits, root writer and port maps -/
noncomputable section
namespace Hierarchy.TraceFactorReceiver.Gather
open ThreeFlat Diagonal RAM
open TraceDistribution

/-- The older five-phase terminal writer spends part of the root-rate
coefficient. Its row-rate term and fixed degree term fit together even at
equality in the true per-root row estimate. -/
theorem old_root_unit (degree rate rows : ℕ) (existsRow : 0<rows) :
    rate*(degree+4*rows+3) ≤ mapPrice degree rate*rows := by
  change _≤rate*(degree+7)*rows
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  have d:=Nat.le_mul_of_pos_right degree existsRow
  rw [Nat.add_mul]
  omega

theorem joint_root_price {F : Type} [Fintype F] [Field F] (rate coefficient rootRate perRoot : ℕ)
    {w levels ended stages depth degree k : ℕ} (T : Diagonal.HistoryContraction.Tree F k)
    (charge ports rootCost : ℕ) (large : max 64 rate≤w) (count : levels≤w)
    (endCount : ended≤ stages) (height : depth≤ stages+4)
    (within : Diagonal.HistoryContraction.Tree.Within depth T) (coeff : 0<coefficient)
    (positive : 0<charge) (localPins : ports≤2*charge)
    (resources : T.resources≤((2*stages+1)*(coefficient*(64*w+1)^3))*charge)
    (terminal : rootCost≤rootRate*
      (degree+4*((2*stages+1)*(coefficient*(64*w+1)^3))+3)*charge) :
    let fee:=(ended+1)*(rate*(coefficient*(64*w+1)^3)*(4*levels+4))
    let setup:=setupPrice stages rate
    fee*charge+(T.replayWork setup+
      (7224+19+1016*T.compile.cells+(9+5*T.compile.internal+22*T.compile.cells))+rootCost)+
        (perRoot+22*ports) ≤
      FactorWork.archiveTariff w depth (setupPrice stages (rate+(perRoot+44)))
        (mapPrice degree rootRate) stages coefficient*charge := by
  intro fee setup
  let rowRate:=((2*stages+1)*(coefficient*(64*w+1)^3))
  let base:=10025+1016*depth+setup
  let maps:=mapPrice degree rootRate
  let loc:=T.replayWork setup+(7224+19+1016*T.compile.cells+(9+5*T.compile.internal+22*T.compile.cells))
  have rows : 0<rowRate:=by dsimp [rowRate];positivity
  have child : loc≤base*(rowRate*charge):=by
    have raw:=tree_tariff T within setup 0
    change loc+0*T.footprint.pins≤(base+0)*T.resources at raw
    simpa only [Nat.zero_mul,Nat.add_zero] using
      (raw.trans (Nat.mul_le_mul_left (base+0) resources))
  have root : rootCost ≤ maps*rowRate*charge:=
    terminal.trans (Nat.mul_le_mul_right charge (old_root_unit degree rootRate rowRate rows))
  have issued:=TraceReceiverVisitArithmetic.joint_fee rate coefficient depth setup maps large count endCount
  have covered : fee*charge+(loc+rootCost)≤FactorWork.archiveTariff w depth setup maps stages coefficient*charge := by
    apply le_trans _ (Nat.mul_le_mul_right charge issued)
    change _≤(fee+(base+maps)*rowRate)*charge
    rw [Nat.add_mul,Nat.add_mul,Nat.add_mul]
    rw [Nat.mul_assoc base rowRate]
    omega
  simpa only [Nat.zero_mul,Nat.add_zero] using charged_maps w depth degree stages coefficient
    rate rootRate perRoot 0 (fee*charge+(loc+rootCost)) charge ports
    height coeff positive localPins covered

end Hierarchy.TraceFactorReceiver.Gather
end

end OAI
