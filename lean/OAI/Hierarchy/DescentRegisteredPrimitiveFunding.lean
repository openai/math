import OAI.Hierarchy.DescentRegisteredTailFunding
import OAI.Hierarchy.DescentDatedPrimitiveCalibration
import OAI.Hierarchy.DescentDatedPrimitiveFunding
import OAI.Hierarchy.DescentFundedPrimitiveWidths
import OAI.Hierarchy.DescentOrdinaryPrimitiveFee

namespace OAI
/-! Native primitive cost at the actual ordinary date with the original registered predecessor. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "feeMultiplier" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
    {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
      (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=GroupStage.depthBound (atRound S.rounds) n f g)
      (t:=S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice}
    (br : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) (fun _ => S.firstWidth G.b p*1)} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)}
    {nonneg : 0 ≤ (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height




open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
variable (op : RotorSpec) (frozen drift degree payload seats hostLanes : ℕ) (ports : DatePorts)
variable (old : ProtocolRAM.Bank) (ordinary : ℕ→Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op g k i p frozen drift degree payload seats ports
local notation "v" => (books).onTicket ticket g frozen p f payload seats hostLanes old ordinary

open DescentDatedOperandReadPipeline
variable (stageFloor : ℕ)
local notation "entry" => (v).datedEntry ports stageFloor
local notation "other" => purchase ((v).withFundedArguments 0 entry).ticketReadGeometry
local notation "ext" => (v).argumentUnitFrom ports stageFloor
local notation "Y" => (v).registeredFrom ports stageFloor
local notation "Q" => SignedStage.atDate G S g k i (NativePitch.incomingHosts S (i+1))
local notation "growth" => 2*(2^S.hostGain*S.radix)
local notation "Z" => NativePitch.incoming S k frozen p f payload ordinary (i+1)


open DescentOrdinaryPalette DescentOrdinaryPrimitiveCheckpoint DescentPrimitivePalette
set_option quotPrecheck false
local notation "Y₀" => (v).registeredEntry ports stageFloor
local notation "b₀" => printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
local notation "L₀" => (Y).paletteShape
local notation "date₀" => DonorDate.atDate G S g k i p
local notation "work₀" => Configuration.workUnit (date₀).degree k (date₀).cap ports.nodes S.retainedNodes b₀
local notation "save₀" => Configuration.returnUnit b₀ S.retainedNodes

include before tail cut in
/-- Public read pitches and both measured batch densities for this exact ticket. -/
theorem registered_primitive_funding (unit : ℕ) (paid : 0<S.censusBits p)
    (purchase₀ : S.censusBits p≤(v).area.unit) (wide : 4*(v).fundedMaxUnit ext*(2^k)≤payload)
    (budget : (2^k)*(v).fundedWorkingUnit ext≤unit)
    (workRoom : 2*work₀≤payload) (returnRoom : 2*save₀≤payload) (workPaid : 4*work₀≤unit)
    (returnPaid : 4*save₀≤unit) : (L₀).Funding payload unit:=by
  have dateEq:=donor_date_eq X G S br ticket before tail cut
  have trueD : (A).degree=(date₀).degree:=congrArg DonorDate.degree dateEq
  have form:=(v).funded_bounds ext paid purchase₀ wide
  have step : 0<2^k:=Nat.two_pow_pos _
  have atWork : (v).fundedWorkingUnit ext≤unit:=(Nat.le_mul_of_pos_left _ step).trans budget
  have hold : DescentOrdinaryPrimitiveCheckpoint.Layout.Filled payload unit ((v).fundedClip ext).working:=
    ⟨form.clipped,form.clipCap,form.fill₁.trans (Nat.mul_le_mul_left _ atWork)⟩
  have next : DescentOrdinaryPrimitiveCheckpoint.Layout.Filled payload unit ((v).fundedClip ext).postPitch:=
    ⟨form.out,(Nat.le_mul_of_pos_right _ step).trans form.outCap,form.fill₂.trans (Nat.mul_le_mul_left _ budget)⟩
  have priorKey:=(v).funded_primitive_prior entry other rfl
  have keys:=(v).funded_primitive_widths entry other
  have configured : (Y).palette=Configuration.atOrdinary G S op p payload (A).degree k
      (date₀).cap ports.nodes S.retainedNodes ports.roleLanes:=by rw [trueD];rfl
  have width : Configuration.workUnit (A).degree k (date₀).cap ports.nodes S.retainedNodes b₀=work₀:=by rw [trueD]
  have nativeWidth : Configuration.workUnit (Y).reference.degree (Y).reference.k (Y).reference.capacity
      (Y).reference.oldNodes (Y).resolver.nodes (Y).paletteShape.primitiveBits=work₀:=width
  exact (Y).primitive_funding (p:=p) (prior:=ports.roleLanes) (h:=payload) (unit:=unit)
    configured hold hold next priorKey keys.1 keys.2.2 (by rwa [nativeWidth]) (by rwa [nativeWidth]) returnRoom returnPaid

include before tail cut in
/-- A common bound on the small numerical parameters of this very date pays for every local donor lane. -/
theorem registered_primitive_factor (J c : ℕ)
    (degRoom : (date₀).degree+1 ≤ scale J c) (capRoom : (date₀).cap ≤ scale J c)
    (blocks : 2^k ≤ scale J c) (newRoom : S.retainedNodes ≤ scale J c) (oldRoom : ports.nodes ≤ scale J c)
    (bits : b₀ ≤ scale J c) (lows : StageVenueTail.OrdinaryRaster.shapes ((date₀).schedule payload seats (S.censusBits p)) ≤ scale J c) :
    let e:=6*c+4
    (Y).primitiveFactor ≤ scale J (25+3*e) ∧ 4*work₀ ≤ scale J (8+3*e) ∧ 4*save₀ ≤ scale J (8+3*e):=by
  intro e
  have dateEq:=donor_date_eq X G S br ticket before tail cut
  have trueD : (A).degree=(date₀).degree:=congrArg DonorDate.degree dateEq
  let a:=scale J c
  have one : 1≤a:=Nat.two_pow_pos _
  have main : 16*a^6 ≤ scale J e:=by
    calc 16*a^6=2^(4+6*(c*(J+1))):=by
           dsimp only [a,scale]
           rw [show 16=2^4 by decide,←pow_mul,←Nat.pow_add]
           congr 1; ring
         _≤_:=Nat.pow_le_pow_right (by decide : 0<2) (by dsimp only [e];nlinarith : 4+6*(c*(J+1))≤e*(J+1))
  have raised (x : ℕ) (small:x≤a) : x ≤ scale J e:=by
    apply small.trans
    change 2^(c*(J+1))≤2^(e*(J+1))
    exact Nat.pow_le_pow_right (by decide : 0<2) (Nat.mul_le_mul_right _ (by dsimp only [e];omega))
  have cone : ((date₀).degree+1)^4*2^k≤a^5:=by
    simpa only [pow_succ a 4] using Nat.mul_le_mul (Nat.pow_le_pow_left degRoom 4) blocks
  have rad : ((date₀).degree+1)^4*2^k ≤ scale J e:=
    calc
      _ ≤ a^5 := cone
      _ ≤ a^6 := by rw [pow_succ a 5]; exact Nat.le_mul_of_pos_right _ one
      _ ≤ 16*a^6 := Nat.le_mul_of_pos_left _ (by decide)
      _ ≤ scale J e := main
  have faces : ((date₀).degree+1)^4 ≤ scale J e:=(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans rad
  have rows : ((date₀).degree+1)^4*2^k*(ports.nodes+(date₀).cap*6) ≤ scale J e:=by
    have semi : ports.nodes+(date₀).cap*6≤7*a:=by omega
    exact (Nat.mul_le_mul cone semi).trans ((by ring_nf;nlinarith only [Nat.zero_le (a^6)] : a^5*(7*a)≤16*a^6).trans main)
  have births : 2^k*(date₀).cap*6 ≤ scale J e:=by
    have bornBound := Nat.mul_le_mul (Nat.le_mul_of_pos_left (2^k) (pow_pos (Nat.succ_pos (date₀).degree) 4))
      (show (date₀).cap*6≤ports.nodes+(date₀).cap*6 by omega)
    exact (by simpa only [Nat.mul_assoc] using bornBound : 2^k*(date₀).cap*6≤((date₀).degree+1)^4*2^k*(ports.nodes+(date₀).cap*6)).trans rows
  have present : (L₀).ports ≤ scale J e:=by change ((A).degree+1)^4≤_;rw [trueD];exact faces
  have candidates : (L₀).candidates ≤ scale J e:=by
    change ((A).degree+1)^4*2^k*(ports.nodes+(date₀).cap*6)≤_;rw [trueD];exact rows
  refine ⟨(Y).primitive_factor_rate J e (raised _ blocks) (raised _ lows) present (raised _ oldRoom) births candidates births,?_⟩
  exact Configuration.units_rate (date₀).degree k (date₀).cap ports.nodes S.retainedNodes b₀ J e (raised _ blocks)
    (raised _ oldRoom) (raised _ newRoom) (raised _ bits) rad rows

/-- The durable node archive supplies the genuine incoming primitive pitch on the next date. -/
theorem returned_primitive_density (J bound : ℕ) (wide : 2*save₀≤payload)
    (rate : 4*save₀ ≤ scale J bound) :
    0<(Y).palette.nextLanes ∧ b₀*S.retainedNodes*(Y).palette.nextLanes≤payload/2 ∧
      payload≤(Y).palette.nextLanes*scale J bound:=by
  have cap:=Configuration.returned_occupancy payload b₀ S.retainedNodes wide
  have incoming : payload≤(Y).palette.nextLanes*(4*save₀):=by
    change payload ≤ Configuration.returned payload b₀ S.retainedNodes*(4*save₀)
    simpa only [Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using cap.2
  exact ⟨cap.1,Configuration.returned_fit ..,incoming.trans (Nat.mul_le_mul_left _ rate)⟩

include radix in
/-- Dates price the concrete returned primitive bank using the selected old and next group counts. -/
theorem registered_primitive_invoice (J rank density unit w ratio : ℕ) (age : i<S.length)
    (room : (L₀).Funding payload unit) (bus : w≤ratio*payload) (factor : (Y).primitiveFactor ≤ scale J rank)
    (unitRate : unit ≤ scale J density) (arity : ports.argumentsPerNode≤(v).vector.operands) :
    invoice ((Y).primitiveUpdate stageFloor Y₀ ((v).registered_match ports stageFloor arity) rfl w)*w≤
      ratio*scale J (rank+density+1)*(hostRows (S.hostSize i)*payload+hostRows (S.hostSize i)*S.groupCount i)+
      ratio*scale J (rank+density+1)*DescentOrdinaryPrimitiveCheckpoint.Layout.control payload:=by
  have cells : S.groupCount i=S.groupCount (i+1)*2^k:=by
    simpa only [Fintype.card_fin,Fintype.card_prod] using Fintype.card_congr (S.groupDigits age radix)
  have mass : (Y).bornBook.groups=(L₀).oldGroups:=cells
  have positive : 0<(L₀).hosts:=Nat.two_pow_pos _
  have levels : 0<2^(k+1)-1:=by rw [pow_succ];have:=Nat.two_pow_pos k;omega
  have lows : 0<(L₀).lows:=Nat.mul_pos levels (Nat.zero_lt_succ _)
  have chip:=((v).funded_primitive_widths entry other).2.1
  have pay:=(Y).primitive_scaled stageFloor Y₀ ((v).registered_match ports stageFloor arity) rfl w payload ratio unit
    J rank density room positive lows rfl mass chip bus factor unitRate
  change _≤_*((L₀).hosts*payload+(L₀).hosts*(S.groupCount (i+1))*2^k)+_ at pay
  rwa [Nat.mul_assoc (L₀).hosts (S.groupCount (i+1)) (2^k),←cells] at pay

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
