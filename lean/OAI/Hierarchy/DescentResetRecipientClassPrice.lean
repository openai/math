import OAI.Hierarchy.DescentResetSelectedPrimitivePrice
import OAI.Hierarchy.DescentResetQuantityFunded

namespace OAI
/-! # The native classification of all attained reset recipients -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentResetActorClass ProtocolRAM
noncomputable section

theorem classCharge_linear (c : Shape) (base : ℕ) :
    classCharge c base≤1000*(1+c.rawHosts+c.hosts*c.parts+c.rawHosts*c.parts):=by
  have one:=DescentVenueQuantityPlanes.padded_length (c.hosts*c.parts)
  have two:=DescentVenueQuantityPlanes.padded_length c.rawHosts
  change (4+10*(c.rawHosts*c.parts)+(4+10*(2*(2^Nat.clog 2 (c.hosts*c.parts))+2^Nat.clog 2 c.rawHosts)))+
    7*(15*(c.rawHosts*c.parts+1)+15*(2*(2^Nat.clog 2 (c.hosts*c.parts))+2^Nat.clog 2 c.rawHosts+1))≤_
  omega

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentSixParty DescentSIMDLookup ProtocolRAM Filter TerminalScale
noncomputable section
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h e prev nextM C packet : ℕ)
    (prior : Prior) (base : ℕ)
local notation "V" => fromBoard G S board k tail age p f g drift degree h e prev (2^e) nextM C packet prior base
local notation "P" => S.hostSize age
local notation "M" => 2^e
local notation "T" => receiptArea h P (chunks (S.groupCount age) M)
local notation "increase" => 2^S.hostGain*S.radix

def recipientFactor (shapes growth : ℕ) := 1000*(1+2*shapes+growth)

theorem recipient_volume (at₀ : ℕ) (radix : S.radix=2^k) (alive : age<S.length) :
    PhysicalReset.FinalInputs.classCharge (V).actorClass at₀≤recipientFactor (V).front.peer.shapes increase*T:=by
  let sh:=(V).front.peer.shapes
  let small:=chunks (S.groupCount (age+1)) M
  let all:=chunks (S.groupCount age) M
  have group : S.groupCount (age+1)*2^k=S.groupCount age:=by
    simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (S.groupDigits alive radix)).symm
  have few : S.groupCount (age+1)≤S.groupCount age:=(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)).trans_eq group
  have fewer : small≤all:=Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right few _) _)
  have part : P*small≤T:=(Nat.mul_le_mul_left _ fewer).trans (by dsimp only [all,receiptArea];omega)
  have one : 1≤T:=by
    have good : 0<(h+1)^3*2^(h/2):=by positivity
    unfold receiptArea
    omega
  have hosts : P≤T:=by unfold receiptArea;omega
  have raw : P*sh≤ sh*T:=by simpa [Nat.mul_comm] using Nat.mul_le_mul_left sh hosts
  have rawRows : (P*sh)*small≤ sh*T:=by simpa only [Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_left sh part
  have next : S.hostSize (age+1)=P*increase:=by simp only [AtomSchedule.hostSize,pow_succ,Nat.mul_assoc]
  have live : S.hostSize (age+1)*small≤ increase*T:=by rw [next];simpa only [Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_left increase part
  have bill:=PhysicalReset.FinalInputs.classCharge_linear (V).actorClass at₀
  change _≤1000*(1+P*sh+S.hostSize (age+1)*small+(P*sh)*small) at bill
  apply bill.trans
  unfold recipientFactor
  dsimp only [sh] at *
  nlinarith only [one,raw,rawRows,live]

theorem recipient_date_price (rate receiver ratio saving : ℕ) :
    ∃lead exponent : ℕ,∀ᶠ h : ℕ in atTop,∀ j shapes growth H groups δ copies N b width rows w fee,
      j≤Nat.log 2 h→2^h≤copies→shapes≤ scale j rate→ growth≤ scale j rate→
      N≤ scale j rate→b≤ scale j rate→width≤ scale j receiver→w≤ratio*h→
      rows*h≤(2+N)*h+groups*(32*N*b+16*width)→fee≤recipientFactor shapes growth*receiptArea h H rows→1≤δ→
      fee*w≤H*h*(lead*scale j exponent)+H*(groups*δ)*(lead*scale j exponent)+copies/(2^j)^saving:=by
  obtain ⟨lead,exponent,room⟩:=clipped_date_price 4000 rate 3 rate receiver ratio saving
  refine ⟨lead,exponent,?_⟩
  filter_upwards [room] with h measured
  intro j sh grow H groups δ copies N b width rows w fee age funded shape growth n bits field word packed cost rad
  have pos : 1≤ scale j rate:=Nat.two_pow_pos _
  have factor : recipientFactor sh grow≤4000*scale j rate:=by unfold recipientFactor;omega
  exact measured j H groups δ copies _ N b width rows w fee age funded factor n bits field word packed cost rad

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentDatedAddressBook DescentSIMDLookup DescentPackedWalsh DescentFallbackPeriod
open ProtocolRAM DescentStaticWordColumn
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d k i D n C f g rate tail h₀ z wire hist : ℕ}
    {bs : P→ℕ} {W : MarkedWorld F d P bs} {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ}
    (r : Reached W G q ε S k i z D wire hist) (rates : ResetRates G S k D n h₀ C f g rate tail)
    (p h drift degree nextM packet oldLanes primitiveLanes printedBits : ℕ)
    (old : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor : ℕ)
local notation "c₀" => S.groupWidth k tail i
local notation "bits₀" => S.localWalshBits p (c₀+k) f (quota S.rounds)
local notation "cut₀" => resetCut S k tail p f h i
local notation "rawCap" => (((capCalendar G.b S.rounds g S.height).take i).prod*256)
local notation "date₀" => PhysicalReset.selected G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
local notation "e₀" => PhysicalReset.receiverCut G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old
local notation "mid₀" => (date₀).successor.middle
local notation "bound₀" => PhysicalReset.selected_cut G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old

local notation "v" => (date₀).successor
local notation "at₀" => (date₀).rebased ((date₀).stageStart floor)
local notation "base₀" => (v).actorEnd at₀
local notation "cal" => capCalendar G.b S.rounds g S.height


local notation "inc" => 2^S.hostGain*S.radix
local notation "classFee" => PhysicalReset.FinalInputs.classCharge (v).actorClass ((v).roleEnd at₀)
theorem selected_recipient_invoice (w localRate receiver ratio saving lead exponent : ℕ)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (live : i<S.length)
    (localRoom : 8*bits₀≤h) (rootRoom : 8*(v).groupWidth≤h)
    (shape : (v).front.peer.shapes≤TerminalScale.scale S.height localRate)
    (growth : inc≤TerminalScale.scale S.height localRate)
    (blocks : 2^k≤TerminalScale.scale S.height localRate) (bw : bits₀≤TerminalScale.scale S.height localRate)
    (units : (v).groupWidth≤TerminalScale.scale S.height receiver)
    (age : S.height≤Nat.log 2 h) (ambient : 2^h≤S.initialSites) (word : w≤ratio*h)
    (quote : ∀j shapes increase H groups δ copies N b width rows w fee,
      j≤Nat.log 2 h→2^h≤copies→shapes≤TerminalScale.scale j localRate→increase≤TerminalScale.scale j localRate→
      N≤TerminalScale.scale j localRate→b≤TerminalScale.scale j localRate→width≤TerminalScale.scale j receiver→w≤ratio*h→
      rows*h≤(2+N)*h+groups*(32*N*b+16*width)→
      fee≤ResetOutput.recipientFactor shapes increase*ResetOutput.receiptArea h H rows→1≤δ→
      fee*w≤H*h*(lead*TerminalScale.scale j exponent)+H*(groups*δ)*(lead*TerminalScale.scale j exponent)+copies/(2^j)^saving) :
    classFee*w≤S.hostSize i*h*(lead*TerminalScale.scale S.height exponent)+
      S.hostSize i*(S.groupCount i*S.radix)*(lead*TerminalScale.scale S.height exponent)+S.initialSites/(2^S.height)^saving:=by
  let issued := ResetOutput.fromBoard G S rates.board k tail i p f g drift degree h e₀ cut₀ (2^e₀)
    nextM C packet (ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old) at₀
  have output : (v) = issued := PhysicalReset.named_successor G S rates.board k tail i p f g drift degree h
    e₀ cut₀ (2^e₀) nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  have volume:=ResetOutput.recipient_volume G S rates.board k tail i p f g drift degree h e₀ cut₀ nextM C packet
    (ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old) at₀ ((v).roleEnd at₀) radix live
  change PhysicalReset.FinalInputs.classCharge issued.actorClass ((v).roleEnd at₀) ≤
    ResetOutput.recipientFactor issued.front.peer.shapes inc *
      ResetOutput.receiptArea h (S.hostSize i) (chunks (S.groupCount i) (2^e₀)) at volume
  rw [← output] at volume
  have rows:=selected_root_rows (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
    live localRoom rootRoom
  rw [←S.group_power baseGroups radix i]
  exact quote S.height (v).front.peer.shapes inc _ _ _ _ (2^k) bits₀ (v).groupWidth _ w _
    age ambient shape growth blocks bw units word rows (by
      have groupEq : (v).middle.rootGroups=S.groupCount i := by
        change 2^c₀=S.groupCount i
        exact S.group_power baseGroups radix i
      have inv := PhysicalReset.selected_inventory G S rates.board k tail i p f g drift degree h
        cut₀ nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
      rw [groupEq,inv.2.2.2]
      exact volume)
    (by rw [radix];exact Nat.two_pow_pos k)

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
