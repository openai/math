import OAI.Hierarchy.DescentMatcherRoomCalendar
import OAI.Hierarchy.DescentMatcherRate
import OAI.Hierarchy.DescentDatedMatcherVolume
import OAI.Hierarchy.DescentDonorMatcherSpace
import OAI.Hierarchy.DescentPrivateDonorActual
import OAI.Hierarchy.DescentDatedOrdinaryPhase
import OAI.Hierarchy.DescentDatedStageVenue

namespace OAI
/-! # Match and retained-count price at the exact ordinary cut of a named terminal branch -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentCompiler.TerminalScale DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ProtocolRAM ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {run : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he run).Choice}
  (br : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R run c)
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies, Fin (Fintype.card (Port pins X.width)))
    (fun _ => S.firstWidth G.b p * 1)} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent))
      (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower) S k i z D
      (S.epochPower ^ S.priceExponent) (S.firstWidth G.b p)}
    {T : StageInput W G rate (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
    {nonneg : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
    {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent))
      (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower) S k (i+1) z' D'
      (S.epochPower ^ S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement

variable (payload seats ratio w floor : ℕ) (input : Operands) (hk : 0<k)
local notation "d₀" => DonorDate.atDate G S g k i p
local notation "board" => S.censusBits p
local notation "a₀" => (d₀).schedule payload seats board
local notation "vals" => measuresAt S G.b p i
local notation "r" => 2^k
local notation "K" => 2^(k+1)
local notation "H" => hostRows (S.hostSize i)
local notation "u₀" => (d₀).amount
local notation "b₀" => (a₀).shapeAt.outputBits*(a₀).lanesAt
local notation "N₀" => (K*H)*chunks (S.groupCount i) (a₀).lanesAt
local notation "prep" => (a₀).nativePhase G hk input vals w floor
variable (bound : ℕ) (atoms : ∀x : Fin (2^k),(input.atoms x.val).work≤bound)
    (fits : ((DonorDate.atDate G S g k i p).schedule payload seats (S.censusBits p)).Space input w floor) (word : w≤ratio*payload) (digits : S.censusBits p≤2^k) (baseGroups : 0<S.baseGroups)
local notation "phase" => prep fits
local notation "work" => DateBill.matchCountRate k (d₀).degree (d₀).cap K bound
variable (bank : Bank) (score : Cell (((DonorDate.atDate G S g k i p).schedule payload seats (S.censusBits p)).shapeAt.outputBits *
    ((DonorDate.atDate G S g k i p).schedule payload seats (S.censusBits p)).lanesAt)→ℕ) (base : ℕ)
local notation "publish" => DescentOrdinaryCountScan.program w bank score base N₀
local notation "feeC" => DescentOrdinaryCountScan.clock b₀ N₀+7*DescentStaticWordColumn.names publish
local notation "invoice" => (((phase).ticks+DescentStaticWordColumn.names (phase).program)+feeC)*w

include ticket before tail cut in
/-- An incoming genuine venue already supplies all roster, actor, hub and atom read addresses.
The signed banks and the last output address are the remaining physical layout fields. -/
theorem matcher_space_at (room : MatcherRoom G S k p payload) (embed : payload≤w)
    (wide : Fintype.card prior.V≤H) (peer : Fin H→Fin D→Option (Fin H)) (m : Memory w)
    (mounted : stageVenue prior wide input (a₀).lanesAt board floor peer m)
    (wires : ∀(x : Fin r) (j : Fin (2*(d₀).cap)), (input.wire x.val j.val).Fits w floor ∧
      (a₀).rows≤(input.wire x.val j.val).size)
    (last : (a₀).rotationEnd input.roster floor<2^w) : (a₀).Space input w floor := by
  have ed:=donor_date_eq X G S br ticket before tail cut
  have degree : (d₀).degree=D := (congrArg DonorDate.degree ed).symm.trans prior.branch
  have amount : 2*(d₀).amount≤payload :=by rw [←ed];exact (room.packed ticket).2
  apply (d₀).matcher_space payload seats board input w floor
    (DonorDate.dated_cap_pos G S g k i p) room.census (Nat.two_pow_pos _) amount embed
  · change DescentPackedColony.Accessible (input.ports (d₀).degree) input.actors H (S.groupCount i)
      (a₀).lanesAt w floor
    rw [degree]
    exact mounted.1
  · exact wires
  · exact mounted.2.2.2.2.1
  · exact fun x=>mounted.2.2.2.2.2.2.2.1 x.val
  · exact last

include ticket before tail cut word atoms digits baseGroups in
theorem matched_count_volume : invoice≤ratio*work*DateBill.volumeBits H (S.groupCount i) payload u₀ := by
  have positive:0<(d₀).cap:=DonorDate.dated_cap_pos G S g k i p
  have gates:=((d₀).matcher_widths board positive digits).2.1
  have eqd:=donor_date_eq X G S br ticket before tail cut
  have measures : (⟨(A).wire,(A).z,(A).hist⟩ : Measures)=vals := by
    unfold measuresAt
    rw [prior.edges,prior.atoms,←ticket.quantum,ticket.grain_on_cut before tail cut br.issuedGrains]
  have groups : 0<S.groupCount i:=by
    change 0<S.baseGroups*S.radix^_
    exact Nat.mul_pos baseGroups (pow_pos (radix.symm ▸ Nat.two_pow_pos k) _)
  change 2^k+(k+3)≤(d₀).amount at gates
  rw [←eqd] at gates
  change 0<(d₀).exponent at hk
  revert score
  revert fits
  revert hk
  rw [←eqd]
  intro hk fits score
  rw [←measures]
  exact DateBill.match_count_bill (ℓ:=Nat.clog 2 (S.hostSize i)) (groups:=S.groupCount i) (A)
    board payload (ticket.donorDate.amount) ratio (DescentTerminalEpochBits.width G.C) seats input floor
    bound atoms groups word gates fits bank score base

include ticket before tail cut word atoms digits baseGroups in
theorem matched_count_invoice (hosts : 0<S.hostSize i) (pages : 2^(payload/2)≤S.hostSize i) :
    invoice≤S.hostSize i*payload*(4*(ratio*work))+
      S.hostSize i*(S.groupCount i*S.radix)*(8*(ratio*work)*u₀) :=
  (matched_count_volume X G S br ticket before tail cut payload seats ratio w floor input hk bound atoms fits
    word digits baseGroups bank score base).trans (DateBill.volume_invoice hosts pages (radix.symm ▸ Nat.two_pow_pos _))

include ticket before tail cut word atoms digits baseGroups in
/-- The public tariff uses the identical exponent and incoming aggregate as the
already budgeted donor port. Only the evaluator work of a prior atom read is new. -/
theorem matched_count_scale {t J resetRate M tailBits e : ℕ}
    (sched : S=stageNumbers G t J f g resetRate M tailBits)
    (field : k=groupBits t J (hostRate t resetRate) (capRate G t g) (cutRate t f g))
    (reads : bound≤ scale J e) (hosts : 0<S.hostSize i) (pages : 2^(payload/2)≤S.hostSize i) :
    let rates:=donorRates G t f g resetRate
    let sCost:=(rates.work+e)*5
    let C₀:=8*ratio*DateBill.matchingConstant
    invoice≤S.hostSize i*payload*(scale J sCost*C₀)+
      S.hostSize i*(S.groupCount i*S.radix)*(scale J (sCost+rates.amount)*C₀) := by
  intro rates sCost C₀
  have gross:=matched_count_invoice X G S br ticket before tail cut payload seats ratio w floor
    input hk bound atoms fits word digits baseGroups bank score base hosts pages
  have know:=selected_input_bounds ticket sched field rates.bounds
  have eqd:=donor_date_eq X G S br ticket before tail cut
  have priceBound : work≤DateBill.matchingConstant*scale J sCost:=by
    rw [←eqd]
    exact DateBill.matchCountRate_scale know.1 reads
  have unitBound : u₀≤ scale J rates.amount:=by
    rw [←eqd]
    change ticket.installedDonorWidth (max (k+3) (Nat.clog 2 ((A).degree+1)))
      (DescentTerminalEpochBits.width G.C)≤ scale J rates.amount
    rw [selected_amount ticket]
    exact know.2
  apply gross.trans
  apply Nat.add_le_add <;> apply Nat.mul_le_mul_left
  · calc
      _ ≤ 4*(ratio*(DateBill.matchingConstant*scale J sCost)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ priceBound)
      _ ≤ _:=by dsimp only [C₀];ring_nf;omega
  · calc
      _ ≤ (8*(ratio*(DateBill.matchingConstant*scale J sCost)))*scale J rates.amount :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ priceBound)) unitBound
      _ = _:=by dsimp only [C₀];rw [←scale_mul];ring


include ticket before tail cut word in
/-- Both the seed and successor compilers emit one direct lookup for the paid atom column.
This specialization fixes its literal instruction cost on the same cofinal calendar and cut. -/
theorem matched_count_paid {t J resetRate M tailBits : ℕ}
    (sched : S=stageNumbers G t J f g resetRate M tailBits)
    (field : k=groupBits t J (hostRate t resetRate) (capRate G t g) (cutRate t f g))
    (room : MatcherRoom G S k p payload) (column : ∀i : Fin r,∃b : Bank,
      input.atoms i.val=ProtocolRAM.Expr.lookup b .row) :
    let rates:=donorRates G t f g resetRate
    let sCost:=(rates.work+3)*5
    let C₀:=8*ratio*DateBill.matchingConstant
    invoice≤S.hostSize i*payload*(scale J sCost*C₀)+
      S.hostSize i*(S.groupCount i*S.radix)*(scale J (sCost+rates.amount)*C₀) := by
  have reads (i : Fin r) : (input.atoms i.val).work≤7 :=by
    obtain ⟨b,hb⟩:=column i
    rw [hb]
    exact le_rfl
  have budget : 7≤ scale J 3 :=by
    exact (by decide : 7≤2^3).trans (Nat.pow_le_pow_right (by decide) (by
      omega))
  exact matched_count_scale X G S br ticket before tail cut payload seats ratio w floor input hk
    7 reads fits word room.census room.groups bank score base sched field budget (room.hosts i) (room.table i)

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
