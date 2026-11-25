import OAI.Hierarchy.DescentDatedTicketPreparationTotal
import OAI.Hierarchy.DescentDatedBookedChip
import OAI.Hierarchy.DescentRegisteredArgumentGatherRoom
import OAI.Hierarchy.DescentRegisteredOrdinaryResultRoom
import OAI.Hierarchy.DescentMaterialIssuedDigit

namespace OAI
/-! The ordinary ticket's incoming memory ranges and word widths on its registered hardware. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentOrdinaryOriginMask
open DescentPacking.PackedMatch.Local.Stage DescentRawCablePanel ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
namespace DatePorts
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (op : RotorSpec) (gain tail p f drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op gain k i p tail drift degree payload seats prior
local notation "base" => (books).onTicket ticket gain tail p f payload seats prior.venue.lanes prior.io.roster ordinary
local notation "floor" => (base).stageStart root

local notation "v" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary

local notation "A" => (base).registeredEntry prior floor
local notation "match₀" => (base).registered_match prior floor (Nat.le_max_left prior.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "e₀" => (v).material
local notation "fmt₀" => (v).ticket.depotShape (v).short
local notation "ports₀" => (A).directory (v) floor (match₀)
local notation "vec₀" => (v).vectorStart floor
local notation "routed₀" => (v).routedStart floor
local notation "mouth₀" => (v).originPortEnd floor
local notation "heads₀" => (v).operandHeaderEnd floor

theorem ordinary_ticket_panel_fields {w : ℕ} (chart : (v).SignedChart) (inlet : (A).Room (v) floor w)
    (digit : (e₀).fieldBits=(v).signedLayout.fieldBits) (cap : 256≤prevWorld.placement.cap) :
    (e₀).oldHosts*chunks (e₀).oldGroups (e₀).oldLanes≤(A).venue.panel.size ∧
    (e₀).oldLanes*max (DepotRAM.totalBits fmt₀) (e₀).fieldBits≤w/2 ∧
    PriorHeader.endAddress (e₀).oldHosts (e₀).groups (e₀).lanes (fmt₀).degree ((v).donorEnd floor)≤(v).operandPathStart floor :=by
  let unit:=(v).ticket.installedDonorWidth (v).short (v).profile
  have raw:=((v).ticket.installed_donor_widths (v).short (v).profile).2.2
  have rawWidth : DepotRAM.totalBits fmt₀≤unit:=by dsimp only [unit];omega
  have digits:=(v).signed_digit_fits cap
  have enough : max (DepotRAM.totalBits fmt₀) (e₀).fieldBits≤unit:=by
    apply max_le rawWidth
    rw [digit]
    exact (Nat.le_add_right ..).trans digits
  have fits:=DescentSIMDLookup.lanes_fit payload unit
  have paid : payload≤w:=inlet.venue.payload
  have before:=(v).into_booked_headers floor
  refine ⟨inlet.venue.oldPanel,(Nat.mul_le_mul_left (e₀).oldLanes enough).trans (fits.trans (Nat.div_le_div_right paid)),?_⟩
  rw [←chart.degree]
  exact before.2.2.2.2.2.trans (before.1.trans (before.2.1.trans (before.2.2.1.trans before.2.2.2.1)))

theorem ordinary_ticket_panel_room {w : ℕ} (chart : (v).SignedChart) (inlet : (A).Room (v) floor w)
    (signed : (v).signed=(v).signedLayout.format payload) (cap : 256≤prevWorld.placement.cap) :
    (e₀).oldHosts*chunks (e₀).oldGroups (e₀).oldLanes≤(A).venue.panel.size ∧
    (e₀).oldLanes*max (DepotRAM.totalBits fmt₀) (e₀).fieldBits≤w/2 ∧
    PriorHeader.endAddress (e₀).oldHosts (e₀).groups (e₀).lanes (fmt₀).degree ((v).donorEnd floor)≤(v).operandPathStart floor :=by
  have digit : (e₀).fieldBits=(v).signedLayout.fieldBits:=by
    change (v).signed.fieldBits=_
    rw [signed]
    rfl
  exact ordinary_ticket_panel_fields prior ticket op gain tail p f drift degree payload seats root ordinary chart inlet digit cap

theorem ordinary_ticket_admission_fields {w : ℕ} (chart : (v).SignedChart)
    (pg : Fin (7*(v).vector.operands)) (inlet : (A).Room (v) floor w)
    (previous : prior.venue.groups=S.groupCount i) (age : i<S.length) (radix : S.radix=2^k)
    (lanes : 0<(v).vector.lanes) (digit : (e₀).fieldBits=(v).signedLayout.fieldBits)
    (cap : 256≤prevWorld.placement.cap) (room : routed₀<2^w)
    (wide : ∀key,((v).wideHead floor chart key).Fits w heads₀) (narrow : ∀key,((v).narrowHead floor key).Fits w heads₀) :
    (v).TicketAdmission floor w chart (A) (match₀) pg :=by
  have geometry:=ordinary_header_dimensions prior ticket op gain tail p f drift degree payload seats root ordinary age radix
  have panels:=ordinary_ticket_panel_fields prior ticket op gain tail p f drift degree payload seats root ordinary chart inlet digit cap
  have available:=(A).gather_ports (v) floor (match₀) inlet previous.symm rfl rfl rfl (Nat.two_pow_pos k) lanes room
  have order:=(v).into_booked_headers floor
  have fromW : vec₀≤routed₀:=(v).vector_before floor
  have toMouth : routed₀≤ mouth₀:=by rw [(v).originPort_span];exact Nat.le_add_right ..
  have oldPanel:=inlet.venue.prior (A).venue.panel (by simp)
  let block : Fin (A).previous.blocks:=⟨0,by rw [(match₀).oldBlocks];exact Nat.two_pow_pos _⟩
  have popEnd : ((A).population (v) floor).outBase≤(A).finish (v) floor:=Nat.le_add_right ..
  have vecEnd := (match₀).atRefs.le.trans order.2.1
  have headEnd := order.2.2.1.trans (order.2.2.2.1.trans order.2.2.2.2.1)
  have transfer : heads₀≤(v).headTransferEnd floor:=by rw [(v).head_transfer_span];exact Nat.le_add_right ..
  have castEnd : (v).headTransferEnd floor≤(v).operandRootBase floor:=Nat.le_add_right ..
  have sorted := DescentPacking.PackedMatch.Local.Stage.Chooser.bank_before (inlet.walk block).roster
    (popEnd.trans (vecEnd.trans (headEnd.trans (transfer.trans castEnd))))
  refine ⟨fun low=>ProtocolRAMGeneratedWrite.fits_mono _ fromW (available pg low).2,?_,geometry.2.2.2,lanes,
    Nat.two_pow_pos k,?_,oldPanel.2.2.trans (order.1.trans (order.2.1.trans order.2.2.1)),
    panels.1,panels.2.1,panels.2.2,wide,narrow,sorted⟩
  · exact DescentPacking.PackedMatch.Local.Stage.Chooser.bank_before ((A).chip_fits (v) floor inlet (match₀))
      (order.2.1.trans (fromW.trans toMouth))
  · intro arg low
    let page := finProdFinEquiv ((0 : Fin 7),arg.cast (match₀).newArgs)
    have mouth := (v).mouthRef_expr (A) (match₀) arg low (v).bornBook.hosts
    have hosts := congrArg (fun h => ((ports₀).refs page low).expr h) geometry.2.1
    exact (congrArg Expr.inputEnd (mouth.trans hosts)).le.trans
      ((PrefixAgreement.inputEnd_of_fits _ (available page low).1).trans (fromW.trans toMouth))

theorem ordinary_ticket_admission {w : ℕ} (chart : (v).SignedChart)
    (pg : Fin (7*(v).vector.operands)) (inlet : (A).Room (v) floor w)
    (previous : prior.venue.groups=S.groupCount i) (age : i<S.length) (radix : S.radix=2^k)
    (lanes : 0<(v).vector.lanes) (signed : (v).signed=(v).signedLayout.format payload)
    (cap : 256≤prevWorld.placement.cap) (room : routed₀<2^w)
    (wide : ∀key,((v).wideHead floor chart key).Fits w heads₀) (narrow : ∀key,((v).narrowHead floor key).Fits w heads₀) :
    (v).TicketAdmission floor w chart (A) (match₀) pg :=by
  have digit : (e₀).fieldBits=(v).signedLayout.fieldBits:=by
    change (v).signed.fieldBits=_
    rw [signed]
    rfl
  exact ordinary_ticket_admission_fields prior ticket op gain tail p f drift degree payload seats root ordinary
    chart pg inlet previous age radix lanes digit cap room wide narrow

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
