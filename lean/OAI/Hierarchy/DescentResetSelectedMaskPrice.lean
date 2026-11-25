import OAI.Hierarchy.DescentResetMaskWordVolume
import OAI.Hierarchy.DescentNamedMaskWork
import OAI.Hierarchy.DescentResetSelectedPrimitivePrice

namespace OAI
/-! # Rank and mask traffic at the selected date's genuine clipped pitch -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler TerminalScale Filter
noncomputable section

theorem mask_factor_le (j rate jobs D shapes growth : ℕ)
    (jm : jobs ≤ scale j rate) (dm : D ≤ scale j rate)
    (sm : shapes ≤ scale j rate) (gm : growth ≤ scale j rate) :
    maskFactor jobs (compiledSourceWork D) shapes growth ≤ 100000000000*scale j (3*rate) := by
  let U := scale j rate
  change jobs ≤ U at jm
  change D ≤ U at dm
  change shapes ≤ U at sm
  change growth ≤ U at gm
  have pos : 1 ≤ U := Nat.two_pow_pos _
  have j' : jobs+1 ≤ 2*U := by omega
  have d' : compiledSourceWork D+1 ≤ 308000*U := by
    unfold compiledSourceWork mixedSourceWork
    omega
  have s' : 2+shapes+growth ≤ 4*U := by omega
  have cube : scale j (3*rate)=U^3 := by
    dsimp only [U,scale]
    rw [←pow_mul]
    congr 1
    ring
  rw [cube]
  calc
    _ ≤ 32768*(2*U)*(308000*U)*(4*U) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 32768 j') d') s'
    _ ≤ _ := by ring_nf; omega

theorem mask_date_price (rate receiver ratio saving : ℕ) :
    ∃lead exponent : ℕ,∀ᶠ h : ℕ in atTop,∀ j jobs D shapes growth H groups δ copies N b width rows w fee,
      j≤ Nat.log 2 h → 2^h≤ copies → jobs≤ scale j rate → D≤ scale j rate →
      shapes≤ scale j rate → growth≤ scale j rate →
      N≤ scale j rate → b≤ scale j rate → width≤ scale j receiver → w≤ ratio*h →
      rows*h≤(2+N)*h+groups*(32*N*b+16*width) →
      fee≤ maskFactor jobs (compiledSourceWork D) shapes growth*receiptArea h H rows → 1≤δ →
      fee*w≤ H*h*(lead*scale j exponent)+H*(groups*δ)*(lead*scale j exponent)+copies/(2^j)^saving := by
  obtain ⟨lead,exponent,priced⟩ := clipped_date_price 100000000000 (3*rate) 3 rate receiver ratio saving
  refine ⟨lead,exponent,?_⟩
  filter_upwards [priced] with h paid
  intro j jobs D shapes growth H groups δ copies N b width rows w fee age stock jm dm sm gm n bits unit word pack bound pos
  exact paid j H groups δ copies _ N b width rows w fee age stock
    (mask_factor_le j rate jobs D shapes growth jm dm sm gm) n bits unit word pack bound pos

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentDatedAddressBook DescentSIMDLookup DescentPackedWalsh DescentFallbackPeriod
open ProtocolRAM DescentStaticWordColumn
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {d k i D n C f g rate tail h₀ : ℕ}
    {G : PoweredGadget F} {S : AtomSchedule} (rates : ResetRates G S k D n h₀ C f g rate tail)
    (p h drift degree nextM packet oldLanes primitiveLanes printedBits : ℕ)
    (old : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor : ℕ)
local notation "cut₀" => resetCut S k tail p f h i
local notation "date₀" => PhysicalReset.selected G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
local notation "e₀" => PhysicalReset.receiverCut G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old
local notation "v" => (date₀).successor
local notation "s" => (v).sheets
local notation "base₀" => (date₀).rebased ((date₀).stageStart floor)
local notation "inc" => 2^S.hostGain*S.radix
local notation "budget" => compiledSourceWork (v).front.peer.oldDegree
local notation "G₀" => chunks (S.groupCount i) (2^e₀)
local notation "H₀" => S.hostSize i

private theorem maskMember (out : ResetOutput) : out.sheets.metaBits*10 ∈ out.receiverUnits := by
  simp [ResetOutput.receiverUnits]

theorem selected_mask_volume {w : ℕ} (u : (date₀).DateInputs ((date₀).stageStart floor) w)
    (radix : S.radix=2^k) (live : i< S.length) (rootRoom : 8*(v).groupWidth≤ h) :
    PhysicalReset.instructionWords (u.masked.code w) u.masked.ticks ≤
      ResetOutput.maskFactor (s).jobs budget (v).front.peer.shapes inc*ResetOutput.receiptArea h H₀ G₀ := by
  have words := u.masked_work
  have exp_eq := selected_root_exponent (i:=i) rates p h drift degree nextM packet oldLanes
    primitiveLanes printedBits old io.wire io.roster floor
  have small := (v).operand_room cut₀ cut₀ (S.groupWidth k tail (i+1)) h rootRoom (Or.inr (maskMember (v)))
  rw [exp_eq] at small
  have fits : 10*u.masked.field*u.masked.lanes≤ h/2 := by
    change 10*(s).metaBits*2^e₀≤h/2
    rw [Nat.mul_comm 10]; exact small
  have cost := PhysicalReset.rank_mask_envelope u h budget words.1 words.2 fits
  have rectangle := ResetOutput.mask_envelope_area G S rates.board k tail i p f g drift degree h e₀
    cut₀ nextM C packet (ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old)
    base₀ radix live
  let pr := ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old
  let out := ResetOutput.fromBoard G S rates.board k tail i p f g drift degree h e₀ cut₀
    (2^e₀) nextM C packet pr base₀
  have outputEq : (v) = out := PhysicalReset.named_successor G S rates.board k tail i p f g drift degree h
    e₀ cut₀ (2^e₀) nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  change 1+out.sheets.hosts*chunks out.sheets.groups out.sheets.lanes+out.front.peer.hosts+2^(h/2) ≤
    (2+out.front.peer.shapes+inc)*ResetOutput.receiptArea h H₀ G₀ at rectangle
  rw [←outputEq] at rectangle
  apply cost.trans
  change 32768*((s).jobs+1)*(budget+1)*
      (1+(s).hosts*chunks (s).groups (s).lanes+(v).front.peer.hosts+2^(h/2)) ≤ _
  simpa only [ResetOutput.maskFactor,Nat.mul_assoc] using
    Nat.mul_le_mul_left (32768*((s).jobs+1)*(budget+1)) rectangle

local notation "bits₀" => S.localWalshBits p ((S.groupWidth k tail i)+k) f (quota S.rounds)

theorem selected_mask_invoice_of_volume (w fee : ℕ)
    (localRate receiver ratio saving lead exponent : ℕ)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (live : i< S.length)
    (localRoom : 8*bits₀≤ h) (rootRoom : 8*(v).groupWidth≤ h)
    (jobs : (s).jobs≤ TerminalScale.scale S.height localRate)
    (oldDegree : (v).front.peer.oldDegree≤ TerminalScale.scale S.height localRate)
    (shapes : (v).front.peer.shapes≤ TerminalScale.scale S.height localRate)
    (growth : inc≤ TerminalScale.scale S.height localRate)
    (blocks : 2^k≤ TerminalScale.scale S.height localRate) (low : bits₀≤ TerminalScale.scale S.height localRate)
    (units : (v).groupWidth≤ TerminalScale.scale S.height receiver)
    (age : S.height≤ Nat.log 2 h) (ambient : 2^h≤ S.initialSites) (word : w≤ ratio*h)
    (quote : ∀ j jcount D shapes growth H groups δ copies N b width rows w fee,
      j≤ Nat.log 2 h → 2^h≤ copies → jcount≤ TerminalScale.scale j localRate → D≤ TerminalScale.scale j localRate →
      shapes≤ TerminalScale.scale j localRate → growth≤ TerminalScale.scale j localRate →
      N≤ TerminalScale.scale j localRate → b≤ TerminalScale.scale j localRate → width≤ TerminalScale.scale j receiver →
      w≤ ratio*h → rows*h≤(2+N)*h+groups*(32*N*b+16*width) →
      fee≤ ResetOutput.maskFactor jcount (compiledSourceWork D) shapes growth*ResetOutput.receiptArea h H rows → 1≤δ →
      fee*w≤ H*h*(lead*TerminalScale.scale j exponent)+H*(groups*δ)*(lead*TerminalScale.scale j exponent)+copies/(2^j)^saving)
    (amount : fee ≤ ResetOutput.maskFactor (s).jobs budget (v).front.peer.shapes inc*ResetOutput.receiptArea h H₀ G₀) :
    fee*w ≤
      H₀*h*(lead*TerminalScale.scale S.height exponent)+
        H₀*(S.groupCount i*S.radix)*(lead*TerminalScale.scale S.height exponent)+S.initialSites/(2^S.height)^saving := by
  have rows := selected_root_rows (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old
    io.wire io.roster floor live localRoom rootRoom
  change chunks (2^(S.groupWidth k tail i)) (v).middle.rootLanes*h ≤ _ at rows
  have inv := PhysicalReset.selected_inventory G S rates.board k tail i p f g drift degree h
    cut₀ nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  rw [inv.2.2.2, S.group_power baseGroups radix i] at rows
  exact quote S.height _ _ _ _ H₀ (S.groupCount i) S.radix S.initialSites (2^k) bits₀ (v).groupWidth G₀ w _
    age ambient jobs oldDegree shapes growth blocks low units word rows amount (by rw [radix];exact Nat.two_pow_pos k)


theorem selected_mask_invoice {w : ℕ} (u : (date₀).DateInputs ((date₀).stageStart floor) w)
    (localRate receiver ratio saving lead exponent : ℕ)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (live : i< S.length)
    (localRoom : 8*bits₀≤ h) (rootRoom : 8*(v).groupWidth≤ h)
    (jobs : (s).jobs≤ TerminalScale.scale S.height localRate)
    (oldDegree : (v).front.peer.oldDegree≤ TerminalScale.scale S.height localRate)
    (shapes : (v).front.peer.shapes≤ TerminalScale.scale S.height localRate)
    (growth : inc≤ TerminalScale.scale S.height localRate)
    (blocks : 2^k≤ TerminalScale.scale S.height localRate) (low : bits₀≤ TerminalScale.scale S.height localRate)
    (units : (v).groupWidth≤ TerminalScale.scale S.height receiver)
    (age : S.height≤ Nat.log 2 h) (ambient : 2^h≤ S.initialSites) (word : w≤ ratio*h)
    (quote : ∀ j jcount D shapes growth H groups δ copies N b width rows w fee,
      j≤ Nat.log 2 h → 2^h≤ copies → jcount≤ TerminalScale.scale j localRate → D≤ TerminalScale.scale j localRate →
      shapes≤ TerminalScale.scale j localRate → growth≤ TerminalScale.scale j localRate →
      N≤ TerminalScale.scale j localRate → b≤ TerminalScale.scale j localRate → width≤ TerminalScale.scale j receiver →
      w≤ ratio*h → rows*h≤(2+N)*h+groups*(32*N*b+16*width) →
      fee≤ ResetOutput.maskFactor jcount (compiledSourceWork D) shapes growth*ResetOutput.receiptArea h H rows → 1≤δ →
      fee*w≤ H*h*(lead*TerminalScale.scale j exponent)+H*(groups*δ)*(lead*TerminalScale.scale j exponent)+copies/(2^j)^saving) :
    PhysicalReset.instructionWords (u.masked.code w) u.masked.ticks*w ≤
      H₀*h*(lead*TerminalScale.scale S.height exponent)+
        H₀*(S.groupCount i*S.radix)*(lead*TerminalScale.scale S.height exponent)+S.initialSites/(2^S.height)^saving := by
  have amount := selected_mask_volume rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old
    io floor u radix live rootRoom
  exact selected_mask_invoice_of_volume rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old
    io floor _ _ localRate receiver ratio saving lead exponent baseGroups radix live localRoom rootRoom jobs oldDegree shapes
    growth blocks low units age ambient word quote amount

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
