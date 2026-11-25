import OAI.Hierarchy.DescentReturnTailCharge
import OAI.Hierarchy.DescentOrdinaryTailShapeRate
import OAI.Hierarchy.DescentNamedSignedReturn

namespace OAI
/-! # The named ordinary date pays its three successor publishers and the final count -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
    {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
      (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=GroupStage.depthBound (atRound S.rounds) n f g)
      (t:=S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice}
    (br : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R run c)
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) (fun _ => S.firstWidth G.b p*1)} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)}
    {nonneg : 0 ≤ (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height



variable (books : OrdinaryBooks) (frozen payload seats hostLanes : ℕ) (old : ProtocolRAM.Bank)
    (ordinary : ℕ→Ordinary)
local notation "v" => books.onTicket ticket g frozen p f payload seats hostLanes old ordinary
local notation "pub" => DonorDate.atDate G S g k i p
local notation "short₀" => max (k+3) (Nat.clog 2 (prior.placement.degree+1))


open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
variable (entry : PhysicalOrdinary.ArgumentEntry (books.onTicket ticket g frozen p f payload seats hostLanes old ordinary)) (other : ℕ)
local notation "extra" => max ((v).fullArgumentUnit entry) other
local notation "Y" => (v).withFundedArguments extra entry
local notation "Q" => SignedStage.atDate G S g k i (NativePitch.incomingHosts S (i+1))
local notation "U" => MaterialProgram.purchased (S.hostSize i) (S.groupCount i) payload
local notation "growth" => 2*(2^S.hostGain*S.radix)

include radix in
theorem ordinary_host_rectangle (live : 0<S.hostSize i) (up : i+1≤S.length) :
    NativePitch.incomingHosts S (i+1)≤S.hostSize i*growth ∧ S.groupCount (i+1)≤S.groupCount i :=by
  have hop : S.hostSize (i+1)=S.hostSize i*(2^S.hostGain*S.radix):=by
    unfold AtomSchedule.hostSize;rw [pow_succ];ring
  have nextPos : 0<S.hostSize (i+1):=by rw [hop,radix];positivity
  refine ⟨(NativePitch.hosts_bounds S (i+1) up).2.trans ((hostRows_double nextPos).trans_eq (by rw [hop];ring)),?_⟩
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by rw [radix];positivity)
    (Nat.sub_le_sub_left (by omega : i≤ i+1) _))

include before tail cut in
theorem native_tail_invoice (floor w ratio u : ℕ) (B : StageVenueTail.Sources) (room : (Y).ResultRoom floor B w)
    (live : 0<S.hostSize i) (bus : w≤ratio*payload)
    (actual : (Y).resolver.lanes=((v).fundedClip extra).postPitch)
    (shape : (Y).resolver.hosts≤NativePitch.incomingHosts S (i+1) ∧
      (Y).resolver.groups≤S.groupCount (i+1) ∧ (Y).resolver.blocks≤2^k)
    (paid : 0<S.censusBits p) (paidFits : S.censusBits p≤(v).area.unit)
    (bought : 4*(v).fundedMaxUnit extra*(2^k)≤payload) (sp : 2*(Q).unit≤payload)
    (priorPrice : (v).unit≤u) (uPos : 0<u) (uWide : 2*u≤payload)
    (credit : 4*(Q).unit≤u ∧ (2^k)*(v).fundedWorkingUnit extra≤u)
    (nextP : 0<(Y).venue.lanes) (nextCap : (Y).venue.lanes≤payload/2)
    (nextRows : (Y).venue.hosts*chunks (Y).venue.groups (Y).venue.lanes*payload≤
      (Y).venue.hosts*payload+(Y).venue.hosts*(Y).venue.groups*u) :
    (Y).tailAmount floor w B room≤ratio*MaterialProgram.tailFactor growth u (2^k)
      (Y).venue.degree (Y).venue.cap (Y).resolver.nodes (Y).resolver.operands*U :=by
  have fee:=(v).funded_argument_bounds extra entry paid paidFits bought
  have vrows:=(v).funded_venue_rows entry g frozen p f hostLanes extra ordinary u rfl paid paidFits bought sp credit.1
    credit.2 nextP nextCap nextRows
  have full : payload≤((v).fundedClip extra).postPitch*u:=fee.fill₂.trans (Nat.mul_le_mul_left _ credit.2)
  have bills:=(v).funded_shelf_rows entry other u uPos uWide actual full
  have cap:=signed_source_capacity X G S br ticket before tail cut
  have widths:=ticket.donorDate.matcher_widths 0 (show 0<ticket.donorDate.cap from by change 0<(A).cap;omega) (Nat.zero_le _)
  have cost:=issued_return_fields X G S br ticket before tail cut books frozen payload seats hostLanes old ordinary
  have cnt : (v).countBits≤payload/2:=by
    have nativeBits : (v).area.shapeAt.outputBits≤DescentPacking.PackedMatch.SixBirths.unit (v).area.shapeAt:=(Nat.le_add_left ..).trans (Nat.le_max_left ..)
    have chunk : (v).area.unit*(v).area.lanesAt≤payload/2:=by
      change (v).area.unit * lanes payload (v).area.unit ≤ payload / 2
      rw [Nat.mul_comm]
      exact lanes_fit payload (v).area.unit
    apply (Nat.mul_le_mul_right _ (nativeBits.trans ?_)).trans chunk
    change DescentPacking.PackedMatch.SixBirths.unit ticket.donorDate.matcher≤(v).unit
    rw [cost.2.1];exact widths.2.2.2.2
  have oldPos : 0<(v).unit:=paid.trans_le paidFits
  have oldWide : 2*(v).unit≤payload:=(Nat.mul_le_mul_left _ priorPrice).trans uWide
  have host:=ordinary_host_rectangle S (radix:=radix) live ticket.hubRows.choose
  have once : (v).area.H≤S.hostSize i*2:=by
    change hostRows (S.hostSize i)≤_
    simpa only [Nat.mul_comm] using hostRows_double live
  exact (Y).tail_paid floor w ratio u _ _ growth (2^k) B room live bus vrows bills oldPos oldWide cnt
    ⟨host.1,shape.1.trans host.1,once⟩ ⟨host.2,shape.2.1.trans host.2,le_rfl⟩ ⟨le_rfl,shape.2.2,le_rfl⟩ priorPrice

include before tail cut in
theorem original_tail_rate {t J reset M final u unitR drift driftR : ℕ}
    (schedule : S=stageNumbers G t J f g reset M final)
    (level : k=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (dr : drift+1≤ scale J driftR) («price» : u≤ scale J unitR)
    (nodes : (Y).resolver.nodes≤S.retainedNodes) (arity : (Y).resolver.operands≤S.retainedArgumentsAt G drift) :
    ∀j∈[growth,u,2^k,(Y).venue.degree,(Y).venue.cap,(Y).resolver.nodes,(Y).resolver.operands],
      j≤ scale J (tailLayoutRate G t f g reset driftR unitR) :=by
  have date:=venue_date_eq X G S br ticket before tail cut frozen payload hostLanes ordinary
  have Dnext : (Y).venue.degree=DescentCompiler.ordinaryDegree (A).degree:=by
    have actual : next.placement.degree=(Y).venue.degree:=congrArg StageVenueTail.Date.degree date
    rw [←actual,next.branch,ticket.nextDegree,prior.branch]
  have Cnext : (Y).venue.cap=2^DescentHostDegree.gainExponent 20 (A).degree*G.b*(A).cap:=by
    have actual : next.placement.cap=(Y).venue.cap:=congrArg StageVenueTail.Date.cap date
    rw [←actual,ticket.capacity,prior.branch]
  let stages := stageNumbers G t J f g reset M final
  have roundsEq : S.rounds = t := by rw [schedule]; rfl
  have age : i ≤ (t+1)*J := ticket.hubRows.choose.le.trans_eq (by rw [schedule]; rfl)
  have nodeRoom : (Y).resolver.nodes ≤ stages.retainedNodes := nodes.trans_eq (congrArg AtomSchedule.retainedNodes schedule)
  have argRoom : (Y).resolver.operands ≤ stages.retainedArgumentsAt G drift :=
    arity.trans_eq (congrArg (fun sched : AtomSchedule => sched.retainedArgumentsAt G drift) schedule)
  have priorCap := prior.valid.capacity
  have capEq : S.capGain = capRate G t g := by rw [schedule]; rfl
  rw [capEq] at priorCap
  have cap := priorCap.trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    (Nat.add_le_add_left (Nat.mul_le_mul_left (capRate G t g) age) 8))
  have degree := ticket.degree_limit
  rw [roundsEq] at degree
  have real := layout_widths G t f g reset J M final (A).degree (A).cap drift driftR u unitR
    (Y).resolver.nodes (Y).resolver.operands degree cap dr «price» nodeRoom argRoom
  let k₀ := groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
  change ∀ j ∈ [2*(2^stages.hostGain*2^k₀),u,2^k₀,DescentCompiler.ordinaryDegree (A).degree,
    2^DescentHostDegree.gainExponent 20 (A).degree*G.b*(A).cap,(Y).resolver.nodes,(Y).resolver.operands],
    j ≤ scale J (tailLayoutRate G t f g reset driftR unitR) at real
  have gain : S.hostGain = stages.hostGain := congrArg AtomSchedule.hostGain schedule
  have same : k = k₀ := level
  rw [Dnext,Cnext,radix,gain]
  rwa [←same] at real

include before tail cut in
theorem named_tail_funding (floor w ratio u : ℕ) (B : StageVenueTail.Sources) (room : (Y).ResultRoom floor B w)
    (live : 0<S.hostSize i) (bus : w≤ratio*payload)
    (actual : (Y).resolver.lanes=((v).fundedClip extra).postPitch)
    (shape : (Y).resolver.hosts≤NativePitch.incomingHosts S (i+1) ∧
      (Y).resolver.groups≤S.groupCount (i+1) ∧ (Y).resolver.blocks≤2^k)
    (paid : 0<S.censusBits p) (paidFits : S.censusBits p≤(v).area.unit)
    (bought : 4*(v).fundedMaxUnit extra*(2^k)≤payload) (sp : 2*(Q).unit≤payload)
    (priorPrice : (v).unit≤u) (uPos : 0<u) (uWide : 2*u≤payload)
    (credit : 4*(Q).unit≤u ∧ (2^k)*(v).fundedWorkingUnit extra≤u)
    (nextP : 0<(Y).venue.lanes) (nextCap : (Y).venue.lanes≤payload/2)
    (nextRows : (Y).venue.hosts*chunks (Y).venue.groups (Y).venue.lanes*payload≤
      (Y).venue.hosts*payload+(Y).venue.hosts*(Y).venue.groups*u)
    {t J reset M last a : ℕ} (schedule : S=stageNumbers G t J f g reset M last)
    (rate : ∀j∈[growth,u,2^k,(Y).venue.degree,(Y).venue.cap,(Y).resolver.nodes,(Y).resolver.operands],j≤ scale J a)
    (age : J≤Nat.log 2 payload) (size : 2^payload≤2*M)
    (pages : ∀J M last i fee : ℕ,J≤Nat.log 2 payload → 2^payload≤2*M →
      let S:=stageNumbers G t J f g reset M last
      let R:=ratio*scale J (endRate a)
      fee≤R*MaterialProgram.purchased (S.hostSize i) (S.groupCount i) payload →
      fee≤S.hostSize i*payload*(R+1)+S.hostSize i*(S.groupCount i*S.radix)*R) :
    let rate₀:=ratio*scale J (endRate a)
    (Y).tailAmount floor w B room≤S.hostSize i*payload*(rate₀+1)+S.hostSize i*(S.groupCount i*S.radix)*rate₀ :=by
  intro rate₀
  have original:=native_tail_invoice X G S br ticket before tail cut books frozen payload seats hostLanes old ordinary
    entry other floor w ratio u B room live bus actual shape paid paidFits bought sp priorPrice uPos uWide credit nextP nextCap nextRows
  have upper : MaterialProgram.tailFactor growth u (2^k) (Y).venue.degree (Y).venue.cap
      (Y).resolver.nodes (Y).resolver.operands≤ scale J (endRate a):=by
    apply (MaterialProgram.tailFactor_le («Q»:=scale J a) (rate _ (by simp)) (rate _ (by simp))
      (rate _ (by simp)) (rate _ (by simp)) (rate _ (by simp)) (rate _ (by simp)) (rate _ (by simp))).trans (end_rate J a)
  have funded:=pages J M last i ((Y).tailAmount floor w B room) age size
  rw [←schedule] at funded
  exact funded (original.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left ratio upper)))

include before tail cut in
theorem named_tail_funded_at (floor w ratio u : ℕ) (B : StageVenueTail.Sources) (room : (Y).ResultRoom floor B w)
    (live : 0<S.hostSize i) (bus : w≤ratio*payload)
    (actual : (Y).resolver.lanes=((v).fundedClip extra).postPitch)
    (shape : (Y).resolver.hosts≤NativePitch.incomingHosts S (i+1) ∧
      (Y).resolver.groups≤S.groupCount (i+1) ∧ (Y).resolver.blocks≤2^k)
    (paid : 0<S.censusBits p) (paidFits : S.censusBits p≤(v).area.unit)
    (bought : 4*(v).fundedMaxUnit extra*(2^k)≤payload) (sp : 2*(Q).unit≤payload)
    (priorPrice : (v).unit≤u) (uPos : 0<u) (uWide : 2*u≤payload)
    (credit : 4*(Q).unit≤u ∧ (2^k)*(v).fundedWorkingUnit extra≤u)
    (nextP : 0<(Y).venue.lanes) (nextCap : (Y).venue.lanes≤payload/2)
    (nextRows : (Y).venue.hosts*chunks (Y).venue.groups (Y).venue.lanes*payload≤
      (Y).venue.hosts*payload+(Y).venue.hosts*(Y).venue.groups*u)
    {t J reset M last drift driftR unitR : ℕ} (schedule : S=stageNumbers G t J f g reset M last)
    (depth : k=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (dr : drift+1≤ scale J driftR) (price : u≤ scale J unitR)
    (nodes : (Y).resolver.nodes≤S.retainedNodes) (arity : (Y).resolver.operands≤S.retainedArgumentsAt G drift)
    (age : J≤Nat.log 2 payload) (size : 2^payload≤2*M)
    (pages : ∀J M last i fee : ℕ,J≤Nat.log 2 payload → 2^payload≤2*M →
      let S:=stageNumbers G t J f g reset M last
      let R:=ratio*scale J (endRate (tailLayoutRate G t f g reset driftR unitR))
      fee≤R*MaterialProgram.purchased (S.hostSize i) (S.groupCount i) payload →
      fee≤S.hostSize i*payload*(R+1)+S.hostSize i*(S.groupCount i*S.radix)*R) :
    let rate₀:=ratio*scale J (endRate (tailLayoutRate G t f g reset driftR unitR))
    (Y).tailAmount floor w B room≤S.hostSize i*payload*(rate₀+1)+S.hostSize i*(S.groupCount i*S.radix)*rate₀ :=by
  have upper:=original_tail_rate X G S br ticket before tail cut books frozen payload seats hostLanes old ordinary
    entry other schedule depth dr price nodes arity
  exact named_tail_funding X G S br ticket before tail cut books frozen payload seats hostLanes old ordinary
    entry other floor w ratio u B room live bus actual shape paid paidFits bought sp priorPrice uPos uWide credit
    nextP nextCap nextRows schedule upper age size pages


end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
