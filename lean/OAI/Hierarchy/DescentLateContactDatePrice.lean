import OAI.Hierarchy.DescentLateContactVolume
import OAI.Hierarchy.DescentResetSelectedPrimitivePrice

namespace OAI
/-! # Uniform bit cost of the late contact fields at the selected physical reset date -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentCompiler.TerminalScale DescentDatedAddressBook.CandidateFront
noncomputable section
variable (A : Shape)
local notation "D" => A.donor
local notation "N" => DescentContactMaskShape.donors D

structure Controls (L : ℕ) : Prop where
  handles : N≤L
  sockets : A.sockets≤L
  shapes : A.shapes≤L
  blocks : A.blocks≤L
  degree : (D).degree≤L

def tariff :=fieldFactor A.sockets (N+1) (A.shapes+1) A.blocks A.operandWork
def diagonalTariff (L : ℕ) :=fieldFactor L (L+1) (L+1) L (3000*(L+1)^2)

theorem tariff_small (j rate : ℕ) (small : A.Controls (scale j rate)) :
    A.tariff≤2^44*scale j (4*rate):=by
  let L:=scale j rate
  have op : A.operandWork≤3000*(L+1)^2:=by
    rcases small with ⟨hN,hQ,hS,hB,hD⟩
    have rad:=DescentVenueQuantityPlanes.padded_length ((D).degree+2)
    change max 68 (1+N*(56+(12+20*A.sockets+(2+2^Nat.clog 2 ((D).degree+2)*20+(12+8*(1+((D).degree+1)*55))))+22))≤_
    apply max_le (by nlinarith only [Nat.zero_le L])
    calc _≤1+L*(56+(12+20*L+(2+(2*(L+2)+1)*20+(12+8*(1+(L+1)*55))))+22):=by
           gcongr; first | assumption | exact rad.trans (by omega)
         _≤_:=by nlinarith only [Nat.zero_le L,Nat.zero_le (L^2)]
  have cheap : A.tariff≤diagonalTariff L:=by
    rcases small with ⟨hN,hQ,hS,hB,hD⟩
    unfold tariff diagonalTariff fieldFactor volumeFactor massFactor massCharge catalogFactor
    gcongr
  have algebra : diagonalTariff L≤2^40*(L+1)^4:=by
    unfold diagonalTariff fieldFactor volumeFactor massFactor massCharge catalogFactor
    ring_nf;omega
  have pos : 1≤L:=Nat.two_pow_pos _
  have raised : L^4=scale j (4*rate):=by
    change (2^(rate*(j+1)))^4=2^((4*rate)*(j+1))
    rw [←pow_mul];congr 1;ring
  calc _≤2^40*(L+1)^4:=cheap.trans algebra
       _≤2^40*(2*L)^4:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
       _=_:=by rw [mul_pow,raised];ring

end
end Hierarchy.DescentContactOutputShape.Shape

namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSixParty DescentCompiler DescentSIMDLookup DescentPackedWalsh ProtocolRAM Filter TerminalScale
noncomputable section

/-- The doubled selected root budget pays the selector combining two separately
purchased field widths, including the projection using a full true block. -/
theorem late_contact_keys (v : ResetOutput) (h : ℕ)
    (lane : v.contactShape.donor.batch=v.receiver.lanes) (next : v.contactShape.batch=v.receiver.lanes)
    (reserve : (v.groupWidth+v.groupWidth)*v.receiver.lanes≤h/2) :
    v.contactShape.KeyRoom h:=by
  let A:=v.contactShape
  let D:=A.donor
  let R:=v.receiver.lanes
  let full:=v.groupWidth
  have grant (t : ℕ) (key : t∈v.rootUnits ∨ t∈v.receiverUnits) : t≤full:=v.groupWidth_fit key
  have room (t : ℕ) (small : t≤full) : t*R≤h/2:=
    (Nat.mul_le_mul_right _ (small.trans (Nat.le_add_right ..))).trans reserve
  have field : D.fieldBits≤full:=grant _ (Or.inl (by simp [rootUnits,D,A,contactShape]))
  have «meta» : A.metaBits≤full:=grant _ (Or.inl (by simp [rootUnits,A,contactShape]))
  have marker : A.markerBits≤full:=grant _ (Or.inl (by simp [rootUnits,A,contactShape]))
  have arity : D.fieldBits*D.boardFields+D.fieldBits≤full:=grant _ (Or.inl (by simp [rootUnits,D,A,contactShape]))
  have width : D.cargoBits+D.cargoBits≤full:=grant _ (Or.inl (by simp [rootUnits,D,A,contactShape]))
  have projection : A.metaBits*A.blocks≤full:=grant _ (Or.inr (by simp [receiverUnits,A,contactShape]))
  have handles:=DescentContactMaskShape.donor_arity D
  constructor
  · rw [lane]
    apply room
    exact (Nat.add_le_add_right (Nat.mul_le_mul_left _ handles) _).trans arity
  · rw [lane];exact room _ marker
  · rw [lane];exact room _ field
  · rw [lane];exact room _ ((Nat.le_add_right ..).trans width)
  · unfold DescentContactOutputShape.Shape.choiceBits
    rw [lane]
    exact max_le ((Nat.mul_le_mul_right _ (Nat.add_le_add field «meta»)).trans reserve)
      ((Nat.mul_le_mul_right _ (Nat.add_le_add «meta» «meta»)).trans reserve)
  · rw [next];exact room _ projection
  · rw [lane];exact room _ «meta»

theorem late_contact_date_price (rate receiver ratio saving : ℕ) :
    ∃lead exponent : ℕ,∀ᶠ h : ℕ in atTop,∀ j (A : DescentContactOutputShape.Shape) H groups δ copies N b width rows w fee,
      j≤Nat.log 2 h→2^h≤copies→A.Controls (scale j rate)→
      N≤ scale j rate→b≤ scale j rate→width≤ scale j receiver→w≤ratio*h→
      rows*h≤(2+N)*h+groups*(32*N*b+16*width)→fee≤A.tariff*receiptArea h H rows→1≤δ→
      fee*w≤H*h*(lead*scale j exponent)+H*(groups*δ)*(lead*scale j exponent)+copies/(2^j)^saving:=by
  obtain ⟨lead,exponent,room⟩:=clipped_date_price (2^44) (4*rate) 3 rate receiver ratio saving
  refine ⟨lead,exponent,?_⟩
  filter_upwards [room] with h measured
  intro j A H groups δ copies N b width rows w fee age funded controls n bits field word packed cost rad
  exact measured j H groups δ copies _ N b width rows w fee age funded (A.tariff_small j rate controls)
    n bits field word packed cost rad

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



local notation "plate" => (v).contactShape
local notation "cost" => (plate).cost ((v).front.donorStart base₀) ((v).trunkEnd at₀) (plate).operandWork

theorem selected_late_contact_invoice (w localRate receiver ratio saving lead exponent : ℕ)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (live : i<S.length)
    (localRoom : 8*bits₀≤h) (rootRoom : 8*(v).groupWidth≤h)
    (controls : (plate).Controls (TerminalScale.scale S.height localRate))
    (blocks : 2^k≤TerminalScale.scale S.height localRate) (bw : bits₀≤TerminalScale.scale S.height localRate)
    (units : (v).groupWidth≤TerminalScale.scale S.height receiver)
    (age : S.height≤Nat.log 2 h) (ambient : 2^h≤S.initialSites) (word : w≤ratio*h)
    (quote : ∀j (A : DescentContactOutputShape.Shape) H groups δ copies N b width rows w fee,
      j≤Nat.log 2 h→2^h≤copies→A.Controls (TerminalScale.scale j localRate)→N≤TerminalScale.scale j localRate→
      b≤TerminalScale.scale j localRate→width≤TerminalScale.scale j receiver→w≤ratio*h→
      rows*h≤(2+N)*h+groups*(32*N*b+16*width)→fee≤A.tariff*ResetOutput.receiptArea h H rows→1≤δ→
      fee*w≤H*h*(lead*TerminalScale.scale j exponent)+H*(groups*δ)*(lead*TerminalScale.scale j exponent)+copies/(2^j)^saving) :
    cost*w≤S.hostSize i*h*(lead*TerminalScale.scale S.height exponent)+
      S.hostSize i*(S.groupCount i*S.radix)*(lead*TerminalScale.scale S.height exponent)+S.initialSites/(2^S.height)^saving:=by
  have eqn := selected_root_exponent (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes
    printedBits old io.wire io.roster floor
  have inv := PhysicalReset.selected_inventory G S rates.board k tail i p f g drift degree h
    cut₀ nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  have cap : 1+((v).groupWidth+(v).groupWidth)*(v).receiver.lanes≤h/2 := by
    rw [inv.2.2.1, ← eqn]
    exact keys_fit (m:=min cut₀ (min cut₀ (S.groupWidth k tail (i+1)))) (v).groupWidth_pos rootRoom
  have twice : ((v).groupWidth+(v).groupWidth)*(v).receiver.lanes≤h/2:=by omega
  have paid:=ResetOutput.late_contact_keys (v) h rfl rfl twice
  have split : S.groupCount (i+1)*2^k=S.groupCount i:=by
    simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (S.groupDigits live radix)).symm
  have grid : (plate).groups*(plate).blocks=(plate).donor.groups:=by
    change S.groupCount (i+1)*2^k=2^c₀
    rw [S.group_power baseGroups radix i]
    exact split
  have lane : (plate).donor.batch≤h:=by
    have pos:(v).groupWidth+(v).groupWidth>0:=Nat.add_pos_left (v).groupWidth_pos _
    exact (Nat.le_mul_of_pos_left _ pos).trans (twice.trans (Nat.div_le_self ..))
  have components:=(plate).cost_volume h ((v).front.donorStart base₀) ((v).trunkEnd at₀)
    (plate).operandWork paid grid rfl (Nat.two_pow_pos _) (Nat.two_pow_pos _) lane
  have rows:=selected_root_rows (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
    live localRoom rootRoom
  rw [←S.group_power baseGroups radix i]
  exact quote S.height (plate) _ _ _ _ (2^k) bits₀ (v).groupWidth _ w _ age ambient controls blocks bw units word
    rows components (by rw [radix];exact Nat.two_pow_pos k)

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
