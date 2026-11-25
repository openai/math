import OAI.Hierarchy.DescentOrdinaryBookMouthRate
import OAI.Hierarchy.DescentOrdinaryDatedEntry
import OAI.Hierarchy.DescentArgumentUnitScale

namespace OAI
/-! # The full argument width purchased by the actual ticket and prior register header -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryBooks
open Computability.BorderVNP.Crossing DescentDatedAddressBook DescentPacking.PackedMatch.Local
open DescentOperandVectorArena DescentSIMDLookup ProtocolRAM
open DescentArgumentWidthArithmetic DescentCompiler.TerminalScale
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

set_option maxHeartbeats 600000 in
/-- Previous archive word size, printed primitive width, and the settled donor and
census widths are the additional registers read by these sixteen dictionaries.
The named calendar already evaluates the other eleven local parameters. -/
theorem argument_book_unit (U : ℕ) (sizes : ∀i,(Lₑ).bookMouthParameters i≤ U)
    (current : src.placement.degree≤(Lₑ).reference.degree)
    (archived : ports.operandBits≤ U) (printed : (Eₑ).roleBits≤ U)
    (panel : (Tₑ).fundedPanelUnit≤ U) (census : S.censusBits p≤ U) :
    (Tₑ).fullArgumentUnit (Eₑ)≤ U^44 :=by
  let V:=(Tₑ).withFundedArguments 0 (Eₑ)
  let A:=(Tₑ).fundedEntry 0 (Eₑ)
  have large : 2048≤ U:=sizes 0
  have pos : 0<U:=by omega
  have small {v : ℕ} (h : v≤ U) : v≤ U^4:=raise pos (one h) (by decide)
  have d : src.placement.degree+1≤ U:= (Nat.add_le_add_right current 1).trans (sizes 1)
  have rad : 2^k≤ U:=sizes 2
  have oldNodes : ports.nodes≤ U:=sizes 3
  have nodes : S.retainedNodes≤ U:=sizes 5
  have low : (Lₑ).vector.lows≤ U:=sizes 6
  have bits : (Lₑ).bornBook.bits≤ U:=sizes 10
  have donor : DescentRawCablePanel.DepotRAM.totalBits (A.chip V).format≤(Tₑ).fundedPanelUnit :=by
    apply le_trans _ ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
    change DescentRawCablePanel.DepotRAM.totalBits (A.chip V).format≤2*DescentRawCablePanel.DepotRAM.totalBits (A.chip V).format+1
    omega
  have digits (n : ℕ) : Nat.clog 2 (n+1)≤ n:=Nat.clog_le_of_le_pow Nat.lt_two_pow_self
  have local_ (i : Fin 23) : V.argumentParameters A i≤ U^4 :=by
    fin_cases i
    · exact small (by omega : 16≤ U)
    · exact small ((Nat.sub_le ports.operandBits 2).trans archived)
    · exact small oldNodes
    · exact max_le (small printed) (small printed)
    · exact small oldNodes
    · exact small ((digits _).trans oldNodes)
    · exact Nat.pow_le_pow_left d 4
    · exact small rad
    · exact small (donor.trans panel)
    · exact small d
    · exact small rad
    · exact small (sizes 4)
    · exact small ((digits _).trans low)
    · exact small bits
    · exact small rad
    · exact small (sizes 4)
    · exact small (sizes 8)
    · exact small (sizes 9)
    · exact raise pos (mul (one bits) (one nodes)) (by decide)
    · exact small ((Nat.le_add_right ..).trans bits)
    · exact small nodes
    · exact small (sizes 7)
    · exact small census
  apply Finset.sup_le
  intro i _
  exact (V.argument_width_bound A (U^4) local_ (small bits) (small bits) i).trans_eq (by ring)

/-- All terms in the exponent are chosen before the epoch length. -/
theorem argument_book_scale (J rate : ℕ) (sizes : ∀i,(Lₑ).bookMouthParameters i≤ DescentCompiler.TerminalScale.scale J rate)
    (current : src.placement.degree≤(Lₑ).reference.degree)
    (archived : ports.operandBits≤ DescentCompiler.TerminalScale.scale J rate) (printed : (Eₑ).roleBits≤ DescentCompiler.TerminalScale.scale J rate)
    (panel : (Tₑ).fundedPanelUnit≤ DescentCompiler.TerminalScale.scale J rate) (census : S.censusBits p≤ DescentCompiler.TerminalScale.scale J rate) :
    (Tₑ).fullArgumentUnit (Eₑ)≤ DescentCompiler.TerminalScale.scale J (44*rate) :=by
  refine (argument_book_unit ticket gain tail p f payload seats hostLanes old ordinary op drift degree ports stageFloor _ sizes current archived printed panel census).trans_eq ?_
  unfold DescentCompiler.TerminalScale.scale;rw [←pow_mul];congr 1;ring

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryBooks

end OAI
