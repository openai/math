import OAI.Hierarchy.DescentOrdinaryBookArgumentScale
import OAI.Hierarchy.DescentSelectorWordScale
import OAI.Hierarchy.DescentFundedOriginChoice

namespace OAI
/-! # Width chosen jointly for the original argument program and all five published selectors -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryBooks
open Computability.BorderVNP.Crossing DescentDatedAddressBook DescentPacking.PackedMatch.Local
open DescentOperandVectorArena DescentSIMDLookup ProtocolRAM DescentArgumentWidthArithmetic
open DescentCompiler.TerminalScale DescentDatedOperandReadPipeline DescentHaloWalkRAM
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
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


/-- Resolving the original raw operand selector raises the required radix exponent by
a fixed factor. Each family shares a single lookup table across all host groups. -/
theorem registered_argument_unit (U : ℕ) (large : 8192≤ U)
    (sizes : ∀i,(Lₑ).bookMouthParameters i≤ U)
    (degreeFits : src.placement.degree≤(Lₑ).reference.degree)
    (capFits : src.placement.cap≤(Lₑ).reference.capacity)
    (archived : ports.operandBits≤ U) (printed : (Eₑ).roleBits≤ U)
    (material : (Tₑ).material.fieldBits≤ U) (census : S.censusBits p≤ U)
    (baseUnit : (Tₑ).fundedMaxUnit 0≤ U) :
    (Tₑ).fundedMaxUnit ((Tₑ).argumentUnitFrom ports stageFloor)≤ U^44 :=by
  let v:=(Tₑ)
  let E:=(Eₑ)
  let W:=v.withFundedArguments 0 E
  let g:=W.ticketReadGeometry
  have pos : 0<U:=by omega
  have small {x : ℕ} (h : x≤ U) : x≤ U^4:=raise pos (one h) (by decide)
  have degreeBound : g.degree+1≤ U:=(Nat.add_le_add_right degreeFits 1).trans (sizes 1)
  have cap : g.cap≤ U:=capFits.trans (sizes 4)
  have paths : g.paths≤ U^4:=Nat.pow_le_pow_left degreeBound 4
  have radix : g.blocks≤ U:=sizes 2
  have b : W.bornBook.bits≤ U:=sizes 10
  have digits : g.digitBits≤ U^4:=by
    apply max_le
    · exact max_le (small material) (small b)
    · apply max_le (small b)
      exact (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self)).trans paths
  have purchased : purchase g≤(U^4)^6:=
    purchase_bound g _ (small large) paths (small radix) (small degreeBound) (small cap) digits
  have full : v.fullArgumentUnit E≤ U^44:=
    argument_book_unit ticket gain tail p f payload seats hostLanes old ordinary op drift degree ports stageFloor
      U sizes degreeFits archived printed ((Nat.le_max_left ..).trans baseUnit) census
  have chosen : v.argumentUnitFrom ports stageFloor≤ U^44:=max_le full
    (purchased.trans (by rw [←pow_mul];exact Nat.pow_le_pow_right pos (by decide)))
  rw [show v.fundedMaxUnit (v.argumentUnitFrom ports stageFloor)=
    max (v.fundedMaxUnit 0) (v.argumentUnitFrom ports stageFloor) by
    simpa only [Nat.zero_max] using v.unit_at 0 (v.argumentUnitFrom ports stageFloor)]
  exact max_le (raise pos (one baseUnit) (by decide)) chosen

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryBooks

end OAI
