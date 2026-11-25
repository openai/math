import OAI.Hierarchy.DescentLateContactDatePrice
import OAI.Hierarchy.DescentLateContactControls
import OAI.Hierarchy.DescentResetRecipientClassPrice
import OAI.Hierarchy.DescentRegisteredResetCharges

namespace OAI
/-! # The scheduled contact and recipient charges of a registered reset -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open ProtocolRAM TerminalScale Filter
noncomputable section
set_option quotPrecheck false

def ContactAmounts (h localRate receiver ratio saving lead exponent : ℕ) : Prop :=
  ∀j (A : DescentContactOutputShape.Shape) H groups δ copies N b width rows w fee,
      j≤Nat.log 2 h→2^h≤copies→A.Controls (scale j localRate)→N≤ scale j localRate→
      b≤ scale j localRate→width≤ scale j receiver→w≤ratio*h→
      rows*h≤(2+N)*h+groups*(32*N*b+16*width)→fee≤A.tariff*ResetOutput.receiptArea h H rows→1≤δ→
      fee*w≤H*h*(lead*scale j exponent)+H*(groups*δ)*(lead*scale j exponent)+copies/(2^j)^saving

def RecipientAmounts (h localRate receiver ratio saving lead exponent : ℕ) : Prop :=
  ∀j shapes increase H groups δ copies N b width rows w fee,
      j≤Nat.log 2 h→2^h≤copies→shapes≤ scale j localRate→increase≤ scale j localRate→
      N≤ scale j localRate→b≤ scale j localRate→width≤ scale j receiver→w≤ratio*h→
      rows*h≤(2+N)*h+groups*(32*N*b+16*width)→
      fee≤ResetOutput.recipientFactor shapes increase*ResetOutput.receiptArea h H rows→1≤δ→
      fee*w≤H*h*(lead*scale j exponent)+H*(groups*δ)*(lead*scale j exponent)+copies/(2^j)^saving

private theorem paid_mono (j H h groups δ extra lead exponent lead' exponent' : ℕ)
    (h₁ : lead≤lead') (h₂ : exponent≤exponent') :
    H*h*(lead*scale j exponent)+H*(groups*δ)*(lead*scale j exponent)+extra≤
    H*h*(lead'*scale j exponent')+H*(groups*δ)*(lead'*scale j exponent')+extra:=by
  have power:scale j exponent≤ scale j exponent':=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right (j+1) h₂)
  gcongr

theorem contact_amounts (rate receiver ratio saving : ℕ) :
    ∃lead exponent : ℕ,∀ᶠ h : ℕ in atTop,
      ContactAmounts h rate receiver ratio saving lead exponent ∧
      RecipientAmounts h rate receiver ratio saving lead exponent:=by
  obtain ⟨a,b,x⟩:=ResetOutput.late_contact_date_price rate receiver ratio saving
  obtain ⟨c,d,y⟩:=ResetOutput.recipient_date_price rate receiver ratio saving
  refine ⟨a+c,b+d,?_⟩
  filter_upwards [x,y] with h ledger roster
  constructor
  · intro j A H groups δ copies N bits width rows w fee age ambient chart blocks low high word area cost radix
    exact (ledger j A H groups δ copies N bits width rows w fee age ambient chart blocks low high word area cost radix).trans
      (paid_mono _ _ _ _ _ _ _ _ _ _ (Nat.le_add_right ..) (Nat.le_add_right ..))
  · intro j shapes inc H groups δ copies N bits width rows w fee age ambient chart growth blocks low high word area cost radix
    exact (roster j shapes inc H groups δ copies N bits width rows w fee age ambient chart growth blocks low high word area cost radix).trans
      (paid_mono _ _ _ _ _ _ _ _ _ _ (Nat.le_add_left ..) (Nat.le_add_left ..))

variable {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {k tail i D n fan f gain rate : ℕ}
    (p drift degree : ℕ) (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ)
    (rates : ResetRates G S k D n fan op.C f gain rate tail) (h : ℕ) (prev : DatePorts) (floor w : ℕ)
local notation "board" => rates.board
local notation "a" => PhysicalReset.scheduled G S board k tail i p f gain drift degree h ordinary op s Z
  prev.operandLanes prev.roleLanes prev.venue prev.io.wire prev.io.roster floor
local notation "room" => ScheduledCodeRoom G S board k tail i p f gain drift degree h ordinary op s Z
  prev.operandLanes prev.roleLanes prev.venue prev.io floor w prev.archive
local notation "plate" => (a).successor.contactShape
local notation "walsh" => S.localWalshBits p (S.groupWidth k tail i+k) f (quota S.rounds)
local notation "nextM" => NativePitch.incoming S k tail p f h ordinary (i+1)
local notation "bits" => DescentPrimitivePalette.printedBits G s Z op
local notation "charge" sc:arg => resetCharges G S board k tail i p f gain drift degree h ordinary op s Z prev floor w sc
local notation "envelope" => fun lead exp saving=>
  S.hostSize i*h*(lead*TerminalScale.scale S.height exp)+S.hostSize i*(S.groupCount i*S.radix)*(lead*TerminalScale.scale S.height exp)+
    S.initialSites/(2^S.height)^saving

/-- Both fields are projected directly from the record supplying the scheduled instruction. -/
theorem contact_charges (space : room) (localRate receiver ratio saving lead exponent : ℕ) (live : i<S.length)
    (localRoom : 8*walsh≤h) (rootRoom : 8*(a).successor.groupWidth≤h)
    (controls : (plate).Controls (scale S.height localRate))
    (growth : 2^S.hostGain*S.radix≤ scale S.height localRate)
    (blocks : 2^k≤ scale S.height localRate) (bw : walsh≤ scale S.height localRate)
    (units : (a).successor.groupWidth≤ scale S.height receiver)
    (age : S.height≤Nat.log 2 h) (ambient : 2^h≤S.initialSites) (word : w≤ratio*h)
    (tables : ContactAmounts h localRate receiver ratio saving lead exponent ∧
      RecipientAmounts h localRate receiver ratio saving lead exponent) :
    (charge space).contact≤(envelope) lead exponent saving ∧ (charge space).classes≤(envelope) lead exponent saving:=by
  have contact := NativePitch.selected_late_contact_invoice (i:=i) rates p h drift degree nextM op.w prev.operandLanes prev.roleLanes
    bits prev.venue prev.io floor w localRate receiver ratio saving lead exponent rates.base rates.radix live
    localRoom rootRoom controls blocks bw units age ambient word tables.1
  have classes := NativePitch.selected_recipient_invoice (i:=i) rates p h drift degree nextM op.w prev.operandLanes prev.roleLanes
    bits prev.venue prev.io floor w localRate receiver ratio saving lead exponent rates.base rates.radix live
    localRoom rootRoom controls.shapes growth blocks bw units age ambient word tables.2
  exact ⟨contact,classes⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
