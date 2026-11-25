import OAI.Hierarchy.DescentOrdinaryMarkWordPrice
import OAI.Hierarchy.DescentSelectedMaterialBill
import OAI.Hierarchy.DescentSelectedReturnRates
import OAI.Hierarchy.DescentIssuedSignedChart
import OAI.Hierarchy.DescentDonorMatcherSpace
import OAI.Hierarchy.DescentIncomingHosts
import OAI.Hierarchy.DescentOrdinarySuccessorInvoice

namespace OAI
/-! # The charged prefix through actual old and new host tables, masks, and all signed digits -/
namespace Hierarchy.DescentDatedAddressBook.SignedStage
theorem blocks_le_unit (q : SignedStage) : 2^q.k≤q.unit := by
  have bits : 0<q.fieldBits := by
    by_contra! z
    have f:=q.field_room.1
    have zero : q.fieldBits=0:=by omega
    rw [zero,pow_zero] at f
    dsimp only [rawAlphabet] at f
    omega
  exact ((Nat.le_mul_of_pos_left (2^q.k) bits).trans (Nat.le_add_right ..)).trans
    (le_max_right q.template.feedUnit _)
end Hierarchy.DescentDatedAddressBook.SignedStage

namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentHostDegree DescentHaloWalkRAM
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup DescentStaticWordColumn ProtocolRAM
noncomputable section
variable {F : Type} [Field F]

private theorem selected_return_rate {P : Type} {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
    {S : AtomSchedule} {price u ε : ℝ} {k i z z' D D' wire hist : ℕ}
    {W : MarkedWorld F d P bits} {prior : Reached W G price ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {p : (T.result he).Choice}
    {n : Normalize ((T.result he).state p)} {next : Reached n.result G price ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink prior he T p n next) {t f gain reset J M tail : ℕ}
    (calendar : S=stageNumbers G t J f gain reset M tail)
    (radix : k=groupBits t J (hostRate t reset) (capRate G t gain) (cutRate t f gain)) :
    let oldUnit:=scale J (donorRates G t f gain reset).amount
    let rates:=signedRates G t f gain reset
    let growth:=2*(2^S.hostGain*S.radix)
    returnPrice prior.placement.degree (2^k) prior.placement.cap growth oldUnit (scale J rates.amount)
      (scale J (materialRate G t f gain reset)) (scale J rates.controls) ≤ scale J (returnRate G t f gain reset) :=by
  subst S
  have age:i≤(t+1)*J:=ticket.hubRows.choose.le
  have cap:=prior.valid.capacity.trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    (Nat.add_le_add_left (Nat.mul_le_mul_left (capRate G t gain) age) 8))
  have cut:=(return_rates G t f gain reset).choose_spec J _ _ ticket.degree_limit cap
  simpa only [radix,stageNumbers,returnRate] using cut

namespace PhysicalOrdinary
variable {P : Type} (v : PhysicalOrdinary F P)

/-- This is the actual first four components of the issued successor invoice. -/
def signedReturnPrefix (floor w : ℕ) (parts adj : Bank) (old : DescentOrdinaryVenueReturn.Sources)
    (input : Dated.Operands) : NativePhase w :=
  let x:=v.withIssuedSigned
  let peers:=DescentOrdinaryVenueReturn.phase old (x.materialEnd floor) v.k v.area.H v.area.D v.venue.hosts v.venue.degree w
  (((x.beforeSignedMaterial floor parts adj w).seq peers).seq (x.mark floor input w)).seq
    (x.signedPhase floor v.issuedSignedChart w)

theorem signed_return_bill {t f g reset J M tail : ℕ}
    (calendar : v.schedule=stageNumbers v.gadget t J f g reset M tail)
    (radix : v.k=groupBits t J (hostRate t reset) (capRate v.gadget t g) (cutRate t f g))
    (short : v.short=max (v.k+3) (Nat.clog 2 (v.prior.placement.degree+1)))
    (profile : v.profile=DescentTerminalEpochBits.width v.gadget.C)
    (level : v.level=Nat.clog 2 (v.schedule.hostSize v.age))
    (nextHosts : v.venue.hosts=NativePitch.incomingHosts v.schedule (v.age+1))
    (degree : v.venue.degree=v.target.placement.degree)
    (matcher : v.unit=v.ticket.donorDate.amount)
    (capacity : 256≤v.prior.placement.cap) (live : 0<v.schedule.hostSize v.age)
    (floor w ratio : ℕ) (parts adj : Bank) (old : DescentOrdinaryVenueReturn.Sources)
    (input : Dated.Operands) (markRoom : v.withIssuedSigned.MarkRoom floor input w)
    (oldRoom : 2*scale J (donorRates v.gadget t f g reset).amount≤v.payload)
    (newRoom : 2*scale J (signedRates v.gadget t f g reset).amount≤v.payload)
    (machine : w≤ratio*v.payload) :
    (v.signedReturnPrefix floor w parts adj old input).wordInvoice ≤
      ratio*scale J (returnRate v.gadget t f g reset)*
        MaterialProgram.purchased (v.schedule.hostSize v.age) (v.schedule.groupCount v.age) v.payload :=by
  let x:=v.withIssuedSigned
  let A:=v.schedule.hostSize v.age
  let H:=v.area.H
  let K:=v.venue.hosts
  let G:=v.schedule.groupCount v.age
  let G':=v.schedule.groupCount (v.age+1)
  let h:=v.payload
  let D:=v.prior.placement.degree
  let cap:=v.prior.placement.cap
  let growth:=2*(2^v.schedule.hostGain*v.schedule.radix)
  let mat:=scale J (materialRate v.gadget t f g reset)
  let U:=scale J (donorRates v.gadget t f g reset).amount
  let sig:=signedRates v.gadget t f g reset
  let V:=scale J sig.amount
  let ctrl:=scale J sig.controls
  let R:=MaterialProgram.purchased A G h
  let C:=MaterialProgram.returnFactor growth U V
  let ink:=markPrice D (2^v.k) cap
  let cost:=returnPrice D (2^v.k) cap growth U V mat ctrl
  have fee : cost ≤ scale J (returnRate v.gadget t f g reset):=selected_return_rate v.ticket calendar radix
  have oldSize : H≤2*A:=by change 2^v.level≤_;rw [level];exact hostRows_double live
  have nextTime : v.age+1≤v.schedule.length:=v.ticket.hubRows.choose
  have rad : v.schedule.radix=2^v.k:=by rw [calendar,radix];rfl
  have hop : v.schedule.hostSize (v.age+1)=A*(2^v.schedule.hostGain*v.schedule.radix):=by
    change v.schedule.initialSites*(2^v.schedule.hostGain*v.schedule.radix)^(v.age+1)=_
    simp only [pow_succ,A,AtomSchedule.hostSize,Nat.mul_assoc]
  have stepLive : 0<v.schedule.hostSize (v.age+1):=by rw [hop,rad];exact Nat.mul_pos live (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
  have newSize : K≤A*growth:=by
    dsimp only [K];rw [nextHosts]
    exact (NativePitch.hosts_bounds v.schedule (v.age+1) nextTime).2.trans
      ((hostRows_double stepLive).trans_eq (by rw [hop];dsimp only [growth];ring))
  have groups : G'≤G:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by rw [rad];exact Nat.two_pow_pos _) (Nat.sub_le_sub_left (by omega : v.age≤v.age+1) _))
  have common : MaterialProgram.population H K G G' h U V≤C*R:=
    MaterialProgram.population_paid live oldSize newSize groups
  have pages : DescentOrdinaryMarkProject.Shape.shared h*h≤2*R:=MaterialProgram.shared_paid A G h
  have first:=v.selected_material_bill calendar radix short profile capacity floor w ratio parts adj oldRoom newRoom machine
  have stage:=v.selected_signed_phase calendar radix floor w ratio degree newRoom machine
  have narrower : (1+2^(h/2)+2*(H+K))*h+4*(H+K)*G'*V≤C*R:=
    (Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.le_add_left G' G)) (Nat.le_add_left V U)) _).trans common
  have ray:=v.ticket.selected_signed_rates calendar radix H K G' h
  have exported : v.signedLayout.unit≤V:=ray.1
  have accepted : v.ticket.donorDate.amount≤U:=by
    change v.ticket.installedDonorWidth (max (v.k+3) (Nat.clog 2 (D+1))) (DescentTerminalEpochBits.width v.gadget.C)≤_
    exact (selected_amount v.ticket).le.trans (selected_input_bounds v.ticket calendar radix (donorRates v.gadget t f g reset).bounds).2
  have marked:=v.ticket.donorDate.matcher_widths 0 (show 0<v.ticket.donorDate.cap from by change 0<v.prior.placement.cap;omega) (Nat.zero_le _)
  have areaPos : 0<v.unit:=by
    rw [matcher]
    have b:=marked.2.1
    have a:=Nat.two_pow_pos v.ticket.donorDate.exponent
    omega
  have handle := marked.2.2.1
  have paint:=x.mark_word_bill floor input markRoom h v.unit v.signedLayout.unit ratio rfl rfl areaPos
    v.signedLayout.positive ((Nat.mul_le_mul_left 2 (matcher.le.trans accepted)).trans oldRoom)
    ((Nat.mul_le_mul_left 2 exported).trans newRoom) (by rw [matcher];exact handle) v.signedLayout.blocks_le_unit machine
  have board : (H+K)*h+(H+K)*G'*(v.unit+v.signedLayout.unit)≤C*R:=by
    apply le_trans _ common
    unfold MaterialProgram.population
    apply Nat.add_le_add
    · exact Nat.mul_le_mul_right h ((Nat.le_mul_of_pos_left (H+K) (by decide : 0 < 2)).trans (Nat.le_add_left ..))
    · exact Nat.mul_le_mul (Nat.mul_le_mul
        (Nat.le_mul_of_pos_left (H+K) (by decide : 0<4)) (Nat.le_add_left G' G))
        (Nat.add_le_add (matcher.le.trans accepted) exported)
  let peers:=DescentOrdinaryVenueReturn.phase old (x.materialEnd floor) v.k H v.area.D K v.venue.degree w
  have deg : v.venue.degree=ordinaryDegree D:=by rw [degree,v.target.branch,v.ticket.nextDegree,←v.prior.branch]
  have peer:=DescentOrdinaryVenueReturn.billed_on_hosts old (x.materialEnd floor) v.k H D K v.venue.degree
    w h ratio A D growth (ordinaryDegree D) machine live oldSize newSize le_rfl deg.le
  have base : A*h≤R:=(Nat.le_add_right (A*h) (A*G)).trans (Nat.le_add_right ..)
  have paidPeer : peers.wordInvoice≤ratio*DescentOrdinaryVenueReturn.hostFee D growth (ordinaryDegree D)*R :=
    peer.trans (by simpa only [Nat.mul_comm (A*h)] using Nat.mul_le_mul_left _ base)
  have paidPaint:=paint.trans (Nat.add_le_add (Nat.mul_le_mul_left _ board) (Nat.mul_le_mul_left _ pages))
  have all:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (first.trans (Nat.mul_le_mul_left _ common)) paidPeer) paidPaint)
    (stage.trans (Nat.mul_le_mul_left _ narrower))
  unfold signedReturnPrefix
  simp only [NativePhase.wordInvoice_seq]
  refine all.trans ?_
  calc
    _ = ratio*cost*R := by
      have combine (r m c rows peer price blocks signed : ℕ) :
          11*r*m*(c*rows) + r*peer*rows +
              (r*price*(4*blocks+12)*(c*rows) + r*price*(2*rows)) +
              r*signed*(c*rows) =
            r*(11*m*c + peer + (price*(4*blocks+12)*c+2*price) + signed*c)*rows := by ring
      exact combine ratio mat C R (DescentOrdinaryVenueReturn.hostFee D growth (ordinaryDegree D))
        ink (2^v.k) ctrl
    _ ≤ _ :=Nat.mul_le_mul_right R (Nat.mul_le_mul_left ratio fee)

end PhysicalOrdinary
end
end Hierarchy.DescentSixParty.Chronology

end OAI
