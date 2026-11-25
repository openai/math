import OAI.Hierarchy.DescentRegisteredArgumentScale
import OAI.Hierarchy.DescentRegisteredSelectorFee
import OAI.Hierarchy.DescentFundedTailDensity

namespace OAI
/-! # Fixed local factors of the attained chronological original-operand selector -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryBooks
open Computability.BorderVNP.Crossing DescentDatedAddressBook DescentPacking.PackedMatch.Local
open DescentOperandVectorArena DescentSIMDLookup ProtocolRAM DescentArgumentWidthArithmetic
open DescentCompiler DescentCompiler.TerminalScale DescentDatedOperandReadPipeline DescentHaloWalkRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule}
    {d k age z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {src : Reached W G q ε S k age z D wire hist} {he : 0≤ ε} {T : StageInput W G u ε}
    {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
    {dst : Reached n.result G q ε S k (age+1) z' D' wire hist}
    (ticket : OrdinaryLink src he T c n dst)
    (gain tail p f payload seats hostLanes : ℕ) (old : Bank)
    (ordinary : ℕ→Stage.Dated.Ordinary)
variable (op : RotorSpec) (drift degree : ℕ) (ports : DatePorts) (stageFloor : ℕ)
local notation "Lₑ" => atDate G S op gain k age p tail drift degree payload seats ports
local notation "Tₑ" => (Lₑ).onTicket ticket gain tail p f payload seats hostLanes old ordinary
local notation "Eₑ" => (Tₑ).datedEntry ports stageFloor


theorem registered_selector_inputs (U : ℕ) (large : 8192≤ U)
    (sizes : ∀i,(Lₑ).bookMouthParameters i≤ U)
    (degreeFits : src.placement.degree≤(Lₑ).reference.degree)
    (capFits : src.placement.cap≤(Lₑ).reference.capacity)
    (material : (Tₑ).material.fieldBits≤ U)
    (funds : (Tₑ).fundedMaxUnit ((Tₑ).argumentUnitFrom ports stageFloor)≤ U) :
    let v:=(Tₑ)
    let W:=v.registeredFrom ports stageFloor
    let u:=2^v.area.k*v.fundedWorkingUnit (v.argumentUnitFrom ports stageFloor)
    ∀j,W.ticketReadGeometry.coefficientInputs 32 u j≤ U^4 :=by
  intro v W u
  let g:=W.ticketReadGeometry
  have pos : 0<U:=by omega
  have small {x : ℕ} (h : x≤ U) : x≤ U^4:=raise pos (one h) (by decide)
  have d : g.degree+1≤ U:=(Nat.add_le_add_right degreeFits 1).trans (sizes 1)
  have cap : g.cap≤ U:=capFits.trans (sizes 4)
  have paths : g.paths≤ U^4:=Nat.pow_le_pow_left d 4
  have radix : 2^v.area.k≤ U:=sizes 2
  have nodes : W.resolver.nodes≤ U:=sizes 5
  have args : W.resolver.operands≤ U:=sizes 7
  have b : W.bornBook.bits≤ U:=sizes 10
  have field : g.digitBits≤ U^4:=max_le (max_le (small material) (small b))
    (max_le (small b) ((Nat.clog_le_of_le_pow Nat.lt_two_pow_self).trans paths))
  have jobs : g.jobs≤ U^4:=raise pos (mul (one radix) (mul (one nodes) (one args))) (by decide)
  have rate : u≤ U^4:=by
    dsimp only [u]
    rw [(v.source_density _).2]
    exact raise pos (mul (one (by omega : 8≤ U)) (mul (one radix) (one funds))) (by decide)
  intro j
  fin_cases j
  · exact small large
  · exact paths
  · exact small radix
  · exact small d
  · exact small cap
  · exact jobs
  · exact field
  · exact small (by omega : 32≤ U)
  · exact rate

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryBooks

end OAI
