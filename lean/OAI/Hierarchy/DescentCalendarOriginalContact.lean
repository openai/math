import OAI.Hierarchy.DescentCalendarContactMeta
import OAI.Hierarchy.DescentResetSenderFieldWidth

namespace OAI
/-! # Original reset sources and calendar widths for the contact mask -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames.Stage DescentStageEdgeReceipt DescentPacking.PackedMatch.Local.Stage
open DescentResetLocalRoster DescentCompiler DescentColonies DescentDenseHostOrder DescentResetPeerUnionRAM DescentResetStemKey
open DescentDatedAddressBook CandidateFront DescentFallbackPeriod DescentFallbackPeriod.Projected DescentContactSenderDate
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentContactDonorFront DescentSharedBookScan
open DescentPaidResidentCount.Reset ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "r" => (Z).k-cc
local notation "Ht" => GroupStage.depthBound D n f g
local notation "H" => S.hostSize i
local notation "J" => 2^cc
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "cap" => (A).cap
local notation "deg" => (A).degree
local notation "leafEq" => congrArg (fun z=>2^(z-cc)) B.keyWidth

variable (M batch : ℕ) (calendar : List ℕ)
local notation "field" => ResetMiddle.fieldWidth D ((calendar.take i).prod*256) n k Ht
variable {bw N K R hm l tiny : ℕ}
    (rc : Receiver deg cap N (Z).n r cc H (S.groupCount i) K R M hm l tiny field Ht bw)
    (book : RootBook (Z).n r deg (2^r) cap field) (space : rc.PreparedFits book) (mem : Memory bw)
local notation "pad" => input.valid.host
local notation "rankV" => input.vertex.trans (Fin.castLEEmb pad)
local notation "axes" => S.resetInputDigits ctl.base ctl.radix i
local notation "gr" => Function.Embedding.refl (Fin (S.groupCount i))
local notation "names" => cableNames k (groupRank ((gr).trans Fin.valEmbedding) ((rankV).trans Fin.valEmbedding))
local notation "natOrder" => input.order.trans Fin.valEmbedding
local notation "don" => DescentIssuedFallbackPanel.donor axes B.frame.basis (B.frame.enough.trans (Nat.sub_le ..))
variable (hdr : OriginalHeader B pad rc book mem) (x : OriginalArrays B pad field)
local notation "mx" => calendar_sender_matrix B M field rc book space mem hdr x
local notation "board" => calendar_sender_values B M field rc book space mem mx
local notation "chip" => fun lo j v block=>DescentResetOppositePayload.widened deg cap field (originalCable B x v block lo j)
local notation "wires" => calendar_sender_raw B field chip


theorem contact_sender_from_original (elapsed : 0< i) (sorted : SourceSorted W input.order)
    (baseRoom : max (max r (2^(Z).n)) (2^r)<2^field) (dimension : (Z).n<field)
    (socketRoom : rootSlots r (2^(Z).n)*(2^(Z).n+2^Ht)<2^field)
    (heightRoom : Ht<2^field) (portRoom : deg≤2^field) :
    ContactSenderRead B calendar pad board wires:=
  ⟨calendar_measured_sender B M field rc book space mem hdr x elapsed sorted baseRoom dimension socketRoom heightRoom portRoom,
    calendar_sender_signs B field x⟩

local notation "L" => 2^(S.groupWidth k tail i+k-cc)
local notation "month" => CandidateFront.menu S ctl.board k tail i D f g M batch C ctl.bitsR calendar

theorem contact_room_of_sizes (paid : cap=(calendar.take i).prod*256)
    (tallies : L*(2*cap)<2^field) (shapes : shelf≤2^field)
    (sockets : rootSlots r (2^(Z).n)*(2^(Z).n+2^Ht)<2^field) :
    ContactFieldRoom B M batch calendar:=by
  have dEq : deg=D:=input.branch
  have marker : (month).contact.outputBits=Nat.clog 2 ((D+1)*shelf+1):=by
    rw [B.public_hub_slots]
    rfl
  have signs : DescentSignedCableCodec.width deg cap≤field:=by
    rw [dEq,paid]
    unfold ResetMiddle.fieldWidth DescentFallbackPeriod.packetField
    exact (Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_left ..))
  refine ⟨tallies,shapes,sockets,?_,signs,?_,?_⟩
  · rw [marker,dEq]
    have small : D*shelf < (D+1)*shelf+1:=by rw [Nat.add_mul];omega
    exact small.trans_le (Nat.le_pow_clog (by decide) _)
  · rw [dEq]
    exact (show D+1<D+2 by omega).trans_le (Nat.le_pow_clog (by decide) _)
  · rw [dEq]
    exact (show D+2<D+3 by omega).trans_le (Nat.le_pow_clog (by decide) _)

theorem contact_field_room (paid : cap=(calendar.take i).prod*256) (portBudget : h≤2^k) :
    ContactFieldRoom B M batch calendar:=by
  apply contact_room_of_sizes B M batch calendar paid
  · have amount : S.groupWidth k tail i+k-cc=k:=by rw [B.commonDepth,Nat.add_sub_cancel_left]
    rw [amount,paid]
    exact ResetMiddle.sender_old_slots ..
  · rw [B.public_hub_slots]
    exact ResetMiddle.sender_shapes D _ n k Ht ctl.board portBudget
  · rw [calendar_residual B,B.dimension]
    exact ResetMiddle.sender_keys ..

theorem measured_sender_from_calendar (elapsed : 0< i) (sorted : SourceSorted W input.order) :
    ContactSenderRead B calendar pad board wires:=by
  let Q:=(calendar.take i).prod*256
  have bitsWide : 2^n<2^field:=by
    apply Nat.pow_lt_pow_right (by decide)
    have bound : n+1≤field:=(Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
    omega
  have kw : 2^k<2^field:=by
    apply Nat.pow_lt_pow_right (by decide)
    have bound : k+1≤field:=(Nat.le_max_left ..).trans (Nat.le_max_right ..)
    omega
  have small : max (max r (2^(Z).n)) (2^r)<2^field:=by
    rw [calendar_residual B,B.dimension]
    exact max_lt (max_lt (Nat.lt_two_pow_self.trans kw) bitsWide) kw
  have hb : Ht<2^field:=by
    have ub : Ht+2≤field:=
      (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
    exact (show Ht<field by omega).trans Nat.lt_two_pow_self
  have dsmall : deg≤2^field:=by
    rw [input.branch]
    have sig : DescentSignedCableCodec.width D Q≤field:=
      (Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_left ..))
    have base : D+1≤2^(Nat.clog 2 (D+1)):=Nat.le_pow_clog (by decide) _
    have step : Nat.clog 2 (D+1)≤DescentSignedCableCodec.width D Q:=by
      exact Nat.le_add_right _ _
    exact (Nat.le_add_right D 1).trans (base.trans (Nat.pow_le_pow_right (by decide) (step.trans sig)))
  apply contact_sender_from_original B M calendar rc book space mem hdr x elapsed sorted small
  · rw [B.dimension]
    have bound : n+1≤field:=(Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
    omega
  · rw [calendar_residual B,B.dimension]
    exact ResetMiddle.sender_keys ..
  · exact hb
  · exact dsmall

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
