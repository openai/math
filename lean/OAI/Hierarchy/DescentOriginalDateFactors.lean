import OAI.Hierarchy.DescentRegisteredMiddleVolume
import OAI.Hierarchy.DescentOriginalReadVolume
import OAI.Hierarchy.DescentOriginMouthVolume
import OAI.Hierarchy.DescentRegisteredHeadCoefficient

namespace OAI
/-! # Local factors on the original twelve-phase ordinary argument entry -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryBooks
open Computability.BorderVNP.Crossing DescentDatedAddressBook DescentPacking.PackedMatch.Local
open DescentGatheredVectorReshape DescentOperandVectorArena DescentSIMDLookup ProtocolRAM DescentArgumentWidthArithmetic
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




/-- The finite literal path enumeration and every earlier operand field are computed
from the real predecessor's bound on its calendar degree and capacity. -/
theorem original_date_factors (U : ℕ) (large : 16384≤ U)
    (sizes : ∀j,(Lₑ).bookMouthParameters j≤ U)
    (degreeFits : src.placement.degree≤(Lₑ).reference.degree)
    (capFits : src.placement.cap≤(Lₑ).reference.capacity) :
    let W:=(Tₑ).registeredFrom ports stageFloor
    let fmt:=W.ticket.depotShape W.short
    let D:=fmt.degree
    let P:=breadth D
    DescentDatedOperandPages.count fmt≤ U^14 ∧ P≤ U^14 ∧ P*(D+1)≤ U^14 ∧
      (P+1)*(30+4*P+4*(P*P))≤ U^14 :=by
  intro W fmt D P
  have d : D+1≤ U:=(Nat.add_le_add_right degreeFits 1).trans (sizes 1)
  have degree : D≤ U:=by omega
  have blocks : fmt.blocks≤ U:=sizes 2
  have cap : fmt.cap≤ U:=capFits.trans (sizes 4)
  have path : P≤ U^4:=Nat.pow_le_pow_left d 4
  have field : DescentDatedOperandPages.count fmt≤ U*(U*(U*4))+U*(U*(3*5)) :=by
    unfold DescentDatedOperandPages.count DescentDatedOperandPages.headerCount DescentDatedOperandPages.anchorCount
    gcongr
  have adj : P*(D+1)≤ U^4*U:=Nat.mul_le_mul path d
  have work : (P+1)*(30+4*P+4*(P*P))≤(U^4+1)*(30+4*U^4+4*(U^4*U^4)):=by gcongr
  have estimates : U*(U*(U*4))+U*(U*(3*5))≤ U^14 ∧ U^4≤ U^14 ∧ U^4*U≤ U^14 ∧
      (U^4+1)*(30+4*U^4+4*(U^4*U^4))≤ U^14 :=by
    generalize U=x at large ⊢
    obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le large
    refine ⟨?_,?_,?_,?_⟩ <;> ring_nf <;> omega
  rcases estimates with ⟨a,b,c,d⟩
  exact ⟨field.trans a,path.trans b,adj.trans c,work.trans d⟩

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryBooks

end OAI
