import OAI.Hierarchy.DescentResetRankedWindowRate
import OAI.Hierarchy.DescentResetSelectedMaskPrice

namespace OAI
/-! # The seven packed exponent bounds and eight physical tables of the selected ranking window -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler TerminalScale Filter DescentResetRankedWindows.Layout
noncomputable section

theorem rank_date_price (rate receiver ratio saving : ℕ) :
    ∃lead exp : ℕ,∀ᶠ h : ℕ in atTop,∀ j X K cap sh growth H groups δ copies N b width rows w fee,
      j≤ Nat.log 2 h → 2^h≤ copies → X≤ scale j rate → K≤ scale j rate → cap≤ scale j rate →
      sh≤ scale j rate → growth≤ scale j rate → N≤ scale j rate → b≤ scale j rate →
      width≤ scale j receiver → w≤ ratio*h → rows*h≤(2+N)*h+groups*(32*N*b+16*width) →
      fee≤ rankedFactor X K cap 7*(2+sh+growth)*receiptArea h H rows → 1≤δ →
      fee*w≤ H*h*(lead*scale j exp)+H*(groups*δ)*(lead*scale j exp)+copies/(2^j)^saving := by
  obtain ⟨r,rank⟩:=ranked_factor_rate (rate+3)
  obtain ⟨lead,exp,all⟩:=clipped_date_price 4 (r+rate) 3 rate receiver ratio saving
  refine ⟨lead,exp,?_⟩
  filter_upwards [all] with h paid
  intro j X K cap sh grow H groups δ copies N b width rows w fee age copiesFit xFit kFit capFit
    shapeFit growFit blocks bits units word rowsFit price delta
  have scaleRoom : scale j rate ≤ scale j (rate+3) := Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_right _ (Nat.le_add_right ..))
  have seven : 7≤ scale j (rate+3) :=
    (by decide : 7≤2^3).trans (Nat.pow_le_pow_right (by decide)
      ((by omega : 3≤ rate+3).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos j))))
  have peer : 2+sh+grow≤4*scale j rate := by
    have : 1≤ scale j rate:=Nat.two_pow_pos _
    omega
  have factor : rankedFactor X K cap 7*(2+sh+grow)≤4*scale j (r+rate) := by
    apply (Nat.mul_le_mul (rank j X K cap 7 (xFit.trans scaleRoom) (kFit.trans scaleRoom)
      (capFit.trans scaleRoom) seven) peer).trans
    unfold scale
    rw [Nat.add_mul,pow_add]
    exact le_of_eq (by ring)
  exact paid j H groups δ copies _ N b width rows w fee age copiesFit factor blocks bits units word rowsFit price delta

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
local notation "G₀" => chunks (S.groupCount i) (2^e₀)
local notation "H₀" => S.hostSize i

local notation "a" => (v).receiver

private theorem rankMembers (out : ResetOutput) :
    out.sheets.metaBits*7+out.ticketBits∈out.receiverUnits ∧
    out.sheets.metaBits*7+out.sheets.metaBits∈out.receiverUnits ∧
    out.ticketBits*5+out.ticketBits*5∈out.receiverUnits ∧
    DescentResetSourceSeekRAM.keyBits 4 out.sheets.candidates+out.sheets.metaBits∈out.receiverUnits ∧
    out.sheets.metaBits*5+out.sheets.metaBits*5∈out.receiverUnits ∧
    8*out.sheets.metaBits+out.sheets.metaBits∈out.receiverUnits := by
  simp [ResetOutput.receiverUnits]

theorem selected_rank_pages (R : (v).RankInputs) (b : ℕ) (rootRoom : 8*(v).groupWidth ≤ h) :
    ((v).rankBook R b).PageBounds (2^(h/2)) := by
  have exp_eq := selected_root_exponent (i:=i) rates p h drift degree nextM packet oldLanes
    primitiveLanes printedBits old io.wire io.roster floor
  have inv := PhysicalReset.selected_inventory G S rates.board k tail i p f g drift degree h
    cut₀ nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  have pay (t : ℕ) (mem : t∈(v).receiverUnits) : 2^(t*(a).lanes) ≤ 2^(h/2) := by
    apply Nat.pow_le_pow_right (by decide)
    rw [inv.2.2.1, ←exp_eq]
    exact (v).operand_room cut₀ cut₀ (S.groupWidth k tail (i+1)) h rootRoom (Or.inr mem)
  obtain ⟨raw,emit,take,returned,heads,signed⟩ := rankMembers (v)
  refine ⟨pay _ raw,pay _ take,pay _ returned,pay _ emit,pay _ heads,pay _ emit,?_⟩
  change 2^(((s).metaBits*8+(s).metaBits)*(a).lanes) ≤ 2^(h/2)
  rw [Nat.mul_comm (s).metaBits 8]
  exact pay _ signed

open DescentResetRankedWindows.Layout
local notation "area" => ResetOutput.receiptArea h H₀ G₀
local notation "factor" => rankedFactor (a).blocks (a).candidates (a).capacity 7

theorem selected_rank_budget_words (R : (v).RankInputs) (b : ℕ)
    (radix : S.radix=2^k) (live : i < S.length) (rootRoom : 8*(v).groupWidth ≤ h) :
    let L:=(v).rankBook R b
    (L.clockBudget 7+7*L.textBudget 7)+(L.tailClock (a).capacity 7+7*L.tailText (a).capacity 7) ≤
      factor*(2+(v).front.peer.shapes+inc)*area := by
  intro L
  let rows := (s).hosts*chunks (s).groups (s).lanes
  let E := 1+rows+(v).front.peer.hosts+2^(h/2)
  have quote := selected_rank_pages rates p h drift degree nextM packet oldLanes primitiveLanes printedBits
    old io floor R b rootRoom
  have power : 2^(h/2) ≤ E := Nat.le_add_left ..
  have pages : L.PageBounds E :=
    ⟨quote.raw.trans power,quote.ticket.trans power,quote.sourceReturn.trans power,quote.key.trans power,
      quote.prefixPage.trans power,quote.assembly.trans power,quote.signedPage.trans power⟩
  have native := L.ranked_volume (a).capacity 7 E ((Nat.two_pow_pos _).trans_le power)
    (show rows ≤ E from ((Nat.le_add_left rows 1).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)) pages
  have last := ResetOutput.mask_envelope_area G S rates.board k tail i p f g drift degree h e₀
    cut₀ nextM C packet (ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old)
    base₀ radix live
  let pr := ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old
  let out := ResetOutput.fromBoard G S rates.board k tail i p f g drift degree h e₀ cut₀
    (2^e₀) nextM C packet pr base₀
  have outputEq : (v) = out := PhysicalReset.named_successor G S rates.board k tail i p f g drift degree h
    e₀ cut₀ (2^e₀) nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  change 1+out.sheets.hosts*chunks out.sheets.groups out.sheets.lanes+out.front.peer.hosts+2^(h/2) ≤
    (2+out.front.peer.shapes+inc)*area at last
  rw [←outputEq] at last
  calc
    _ ≤ factor*E := native
    _ ≤ factor*((2+(v).front.peer.shapes+inc)*area) := Nat.mul_le_mul_left _ last
    _ = _ := (Nat.mul_assoc ..).symm

/-- Both rank scans and the signed output window are paid at the hardware-selected lane width. -/
theorem selected_rank_words {w : ℕ} (q : (v).Sectors) (start b D₀ : ℕ)
    (radix : S.radix=2^k) (live : i< S.length) (rootRoom : 8*(v).groupWidth ≤ h) :
    let R:=(v).linkedRankInputs q start
    let L:=(v).rankBook R b
    let render:=(v).renderFromRanks R b
    PhysicalReset.instructionWords (L.program w) L.time+
        PhysicalReset.instructionWords ((v).renderProgram render b D₀ w) ((v).renderTicks render b D₀) ≤
      factor*(2+(v).front.peer.shapes+inc)*area := by
  intro R L render
  have costOld : ∀x j,(L.header x j).work ≤ 7 := fun _ _=>le_rfl
  have costNew : ∀x j,(L.original x j).work ≤ 7 := fun _ _=>le_rfl
  have book := L.invoice (w:=w) 7 costOld costNew
  have signedInvoice := L.tail_invoice (w:=w) 7 costOld costNew D₀ (a).capacity
  change (v).renderTicks render b D₀ ≤ _ ∧
    DescentStaticWordColumn.names ((v).renderProgram render b D₀ w) ≤ _ at signedInvoice
  calc
    _ ≤ (L.clockBudget 7+7*L.textBudget 7)+(L.tailClock (a).capacity 7+7*L.tailText (a).capacity 7) := by
      apply Nat.add_le_add
      · exact Nat.add_le_add book.1 (Nat.mul_le_mul_left _ book.2)
      · exact Nat.add_le_add signedInvoice.1 (Nat.mul_le_mul_left _ signedInvoice.2)
    _ ≤ _ := selected_rank_budget_words rates p h drift degree nextM packet oldLanes primitiveLanes
      printedBits old io floor R b radix live rootRoom

local notation "lowBits" => S.localWalshBits p ((S.groupWidth k tail i)+k) f (quota S.rounds)

theorem selected_rank_invoice {w : ℕ} (q : (v).Sectors) (start b D₀ : ℕ)
    (rate₀ receiver ratio saving lead exp : ℕ)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (live : i< S.length)
    (localRoom : 8*lowBits ≤ h) (rootRoom : 8*(v).groupWidth≤ h)
    (xFit : (a).blocks≤ TerminalScale.scale S.height rate₀)
    (kFit : (a).candidates≤ TerminalScale.scale S.height rate₀)
    (capFit : (a).capacity≤ TerminalScale.scale S.height rate₀)
    (shapes : (v).front.peer.shapes≤ TerminalScale.scale S.height rate₀)
    (growth : inc≤ TerminalScale.scale S.height rate₀) (blocks : 2^k≤ TerminalScale.scale S.height rate₀)
    (bits : lowBits≤ TerminalScale.scale S.height rate₀) (units : (v).groupWidth≤ TerminalScale.scale S.height receiver)
    (age : S.height≤ Nat.log 2 h) (size : 2^h≤ S.initialSites) (word : w≤ ratio*h)
    (fund : ∀j X K cap sh grow H groups δ copies N b width rows w fee,
      j≤ Nat.log 2 h → 2^h≤ copies → X≤ TerminalScale.scale j rate₀ → K≤ TerminalScale.scale j rate₀ →
      cap≤ TerminalScale.scale j rate₀ → sh≤ TerminalScale.scale j rate₀ → grow≤ TerminalScale.scale j rate₀ →
      N≤ TerminalScale.scale j rate₀ → b≤ TerminalScale.scale j rate₀ → width≤ TerminalScale.scale j receiver →
      w≤ ratio*h → rows*h≤(2+N)*h+groups*(32*N*b+16*width) →
      fee≤ rankedFactor X K cap 7*(2+sh+grow)*ResetOutput.receiptArea h H rows → 1≤δ →
      fee*w≤ H*h*(lead*TerminalScale.scale j exp)+H*(groups*δ)*(lead*TerminalScale.scale j exp)+copies/(2^j)^saving) :
    let R:=(v).linkedRankInputs q start
    let L:=(v).rankBook R b
    let render:=(v).renderFromRanks R b
    (PhysicalReset.instructionWords (L.program w) L.time+
     PhysicalReset.instructionWords ((v).renderProgram render b D₀ w) ((v).renderTicks render b D₀))*w ≤
      H₀*h*(lead*TerminalScale.scale S.height exp)+
      H₀*(S.groupCount i*S.radix)*(lead*TerminalScale.scale S.height exp)+S.initialSites/(2^S.height)^saving := by
  have rows := selected_root_rows (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old
    io.wire io.roster floor live localRoom rootRoom
  have packed : G₀*h≤(2+2^k)*h+S.groupCount i*(32*2^k*lowBits+16*(v).groupWidth) := by
    change chunks (2^(S.groupWidth k tail i)) (v).middle.rootLanes*h ≤ _ at rows
    have inv := PhysicalReset.selected_inventory G S rates.board k tail i p f g drift degree h
      cut₀ nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
    rw [inv.2.2.2, S.group_power baseGroups radix i] at rows
    exact rows
  have price := selected_rank_words (w:=w) rates p h drift degree nextM packet oldLanes primitiveLanes
    printedBits old io floor q start b D₀ radix live rootRoom
  exact fund S.height _ _ _ _ _ H₀ (S.groupCount i) S.radix S.initialSites (2^k) lowBits (v).groupWidth
    G₀ w _ age size xFit kFit capFit shapes growth blocks bits units word packed price (by rw [radix];exact Nat.two_pow_pos k)

theorem selected_rank_budget_invoice {w : ℕ} (R : (v).RankInputs) (b : ℕ)
    (rate₀ receiver ratio saving lead exp : ℕ)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (live : i< S.length)
    (localRoom : 8*lowBits ≤ h) (rootRoom : 8*(v).groupWidth≤ h)
    (xFit : (a).blocks≤ TerminalScale.scale S.height rate₀)
    (kFit : (a).candidates≤ TerminalScale.scale S.height rate₀)
    (capFit : (a).capacity≤ TerminalScale.scale S.height rate₀)
    (shapes : (v).front.peer.shapes≤ TerminalScale.scale S.height rate₀)
    (growth : inc≤ TerminalScale.scale S.height rate₀) (blocks : 2^k≤ TerminalScale.scale S.height rate₀)
    (bits : lowBits≤ TerminalScale.scale S.height rate₀) (units : (v).groupWidth≤ TerminalScale.scale S.height receiver)
    (age : S.height≤ Nat.log 2 h) (size : 2^h≤ S.initialSites) (word : w≤ ratio*h)
    (fund : ∀j X K cap sh grow H groups δ copies N b width rows w fee,
      j≤ Nat.log 2 h → 2^h≤ copies → X≤ TerminalScale.scale j rate₀ → K≤ TerminalScale.scale j rate₀ →
      cap≤ TerminalScale.scale j rate₀ → sh≤ TerminalScale.scale j rate₀ → grow≤ TerminalScale.scale j rate₀ →
      N≤ TerminalScale.scale j rate₀ → b≤ TerminalScale.scale j rate₀ → width≤ TerminalScale.scale j receiver →
      w≤ ratio*h → rows*h≤(2+N)*h+groups*(32*N*b+16*width) →
      fee≤ rankedFactor X K cap 7*(2+sh+grow)*ResetOutput.receiptArea h H rows → 1≤δ →
      fee*w≤ H*h*(lead*TerminalScale.scale j exp)+H*(groups*δ)*(lead*TerminalScale.scale j exp)+copies/(2^j)^saving) :
    let L:=(v).rankBook R b
    ((L.clockBudget 7+7*L.textBudget 7)+(L.tailClock (a).capacity 7+7*L.tailText (a).capacity 7))*w ≤
      H₀*h*(lead*TerminalScale.scale S.height exp)+
      H₀*(S.groupCount i*S.radix)*(lead*TerminalScale.scale S.height exp)+S.initialSites/(2^S.height)^saving := by
  have rows := selected_root_rows (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old
    io.wire io.roster floor live localRoom rootRoom
  have packed : G₀*h≤(2+2^k)*h+S.groupCount i*(32*2^k*lowBits+16*(v).groupWidth) := by
    change chunks (2^(S.groupWidth k tail i)) (v).middle.rootLanes*h ≤ _ at rows
    have inv := PhysicalReset.selected_inventory G S rates.board k tail i p f g drift degree h
      cut₀ nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
    rw [inv.2.2.2, S.group_power baseGroups radix i] at rows
    exact rows
  have price := selected_rank_budget_words rates p h drift degree nextM packet oldLanes primitiveLanes
    printedBits old io floor R b radix live rootRoom
  exact fund S.height _ _ _ _ _ H₀ (S.groupCount i) S.radix S.initialSites (2^k) lowBits (v).groupWidth
    G₀ w _ age size xFit kFit capFit shapes growth blocks bits units word packed price (by rw [radix];exact Nat.two_pow_pos k)

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
