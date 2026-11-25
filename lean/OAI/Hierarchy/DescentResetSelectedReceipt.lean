import OAI.Hierarchy.DescentNamedReceivedPrice
import OAI.Hierarchy.DescentResetSelectedAtlasTraffic
import OAI.Hierarchy.DescentResetReceiptDatePrice

namespace OAI
/-! An invoice for the selected physical actuator-to-trunk program on its own
mounted rotor, rank pages, actor labels and admitted previous venue. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentDatedAddressBook DescentSIMDLookup DescentPackedWalsh DescentFallbackPeriod
open ProtocolRAM DescentStaticWordColumn
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d k i D n C f g rate tail h₀ z wire hist : ℕ}
    {bs : P→ℕ} {W : MarkedWorld F d P bs} {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ}
    (r : Reached W G q ε S k i z D wire hist) (rates : ResetRates G S k D n h₀ C f g rate tail)
    (p h drift degree nextM packet oldLanes primitiveLanes printedBits : ℕ)
    (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ)
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

private theorem within_old_cut : cut₀ ≤ c₀ := by
  have lo : laneBits (c₀+k) h bits₀ ≤ c₀+k:=Nat.min_le_left _ _
  change laneBits (c₀+k) h bits₀-k ≤ c₀
  omega

local notation "operands" count "," w => PhysicalReset.namedOriginals G S rates.board k tail i p f g drift degree h
  e₀ cut₀ (2^e₀) nextM C packet oldLanes primitiveLanes printedBits old io floor w
  (bound₀).2.1 (bound₀).1 (within_old_cut (S:=S) (k:=k) (tail:=tail) (i:=i) (p:=p) (f:=f) (h:=h)) count
local notation "scene" count "," w => (v).issuedScene at₀ (operands count, w)
local notation "U" => CandidateFront.sourceLimit (v).front.peer.shapes (500+23*(mid₀).stencil.m+64)
local notation "gain" => 2^S.hostGain*S.radix

def actual_receipt_window (localRate : ℕ) (blocks : 2^k ≤ TerminalScale.scale S.height localRate)
    (cap : rawCap ≤ TerminalScale.scale S.height localRate) (work : U ≤ TerminalScale.scale S.height localRate)
    (increase : gain ≤ TerminalScale.scale S.height localRate) :
    ResetOutput.ReceiptAt rates.board old.degree f g localRate S.height :=
  ⟨v,S,k,tail,i,2^e₀,2^e₀,(v).front.stemField,(v).front.metaBits,C,packet,U,gain,cal,
    rfl,blocks,cap,work,increase⟩

theorem selected_received_invoice (count : Bank) (w localRate receiver ratio saving lead exponent : ℕ)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (live : i < S.length) (hosts : 0 < S.hostSize i)
    (localRoom : 8*bits₀ ≤ h) (rootRoom : 8*(v).groupWidth ≤ h)
    (blocks : 2^k ≤ TerminalScale.scale S.height localRate)
    (cap : rawCap ≤ TerminalScale.scale S.height localRate) (work : U ≤ TerminalScale.scale S.height localRate)
    (increase : gain ≤ TerminalScale.scale S.height localRate) (bw : bits₀ ≤ TerminalScale.scale S.height localRate)
    (units : (v).groupWidth ≤ TerminalScale.scale S.height receiver)
    (age : S.height ≤ Nat.log 2 h) (ambient : 2^h ≤ S.initialSites) (word : w ≤ ratio*h)
    (quote : ∀j (a : ResetOutput.ReceiptAt rates.board old.degree f g localRate j),∀ H groups δ copies N b width rows w fee,
      j ≤ Nat.log 2 h → 2^h ≤ copies → N ≤ TerminalScale.scale j localRate → b ≤ TerminalScale.scale j localRate →
      width ≤ TerminalScale.scale j receiver → w ≤ ratio*h → rows*h ≤ (2+N)*h+groups*(32*N*b+16*width) →
      fee ≤ a.v.receiptFactor a.gain a.source*ResetOutput.receiptArea h H rows → 1≤δ →
      fee*w ≤ H*h*(lead*TerminalScale.scale j exponent)+H*(groups*δ)*(lead*TerminalScale.scale j exponent)+copies/(2^j)^saving)
    (space : (v).front.SceneRoom base₀ (scene count, w) w) :
    let receipt:=(v).front.received base₀ (scene count, w) space
    (receipt.ticks+7*names receipt.program)*w ≤ S.hostSize i*h*(lead*TerminalScale.scale S.height exponent)+
      S.hostSize i*(S.groupCount i*S.radix)*(lead*TerminalScale.scale S.height exponent)+S.initialSites/(2^S.height)^saving := by
  let point:=actual_receipt_window rates p h drift degree nextM packet oldLanes primitiveLanes printedBits
    old io floor localRate blocks cap work increase
  have orig:=PhysicalReset.named_received_price G S rates.board k tail i p f g drift degree h e₀ cut₀ (2^e₀) nextM C packet
    oldLanes primitiveLanes printedBits old io floor w (bound₀).2.1 (bound₀).1
    (within_old_cut (S:=S) (k:=k) (tail:=tail) (i:=i) (p:=p) (f:=f) (h:=h)) count space
  let pr := ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old
  let out := ResetOutput.fromBoard G S rates.board k tail i p f g drift degree h e₀ cut₀
    (2^e₀) nextM C packet pr at₀
  have outputEq : (v) = out := PhysicalReset.named_successor G S rates.board k tail i p f g drift degree h
    e₀ cut₀ (2^e₀) nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  have exp_eq := selected_root_exponent (i:=i) rates p h drift degree nextM packet oldLanes
    primitiveLanes printedBits old io.wire io.roster floor
  have inv := PhysicalReset.selected_inventory G S rates.board k tail i p f g drift degree h
    cut₀ nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  have bound := ResetOutput.received_volume G S rates.board k tail i p f g drift degree h e₀ cut₀ nextM C packet
    pr at₀ base₀ U baseGroups radix live hosts (fun x used => by
      change x ∈ out.rootUnits ∨ x ∈ out.receiverUnits at used
      change x*out.receiver.lanes ≤ _
      rw [←outputEq] at used ⊢
      have read := (v).operand_room cut₀ cut₀ (S.groupWidth k tail (i+1)) h rootRoom used
      rw [exp_eq] at read
      rw [inv.2.2.1]
      exact read)
  change out.front.receivedBill base₀ U ≤ out.receiptFactor gain U *
    ResetOutput.receiptArea h (S.hostSize i) (chunks (S.groupCount i) (2^e₀)) at bound
  rw [←outputEq] at bound
  have rows:=selected_root_rows (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old
    io.wire io.roster floor live localRoom rootRoom
  change chunks (2^c₀) (v).middle.rootLanes*h ≤ _ at rows
  rw [inv.2.2.2] at rows
  rw [←S.group_power baseGroups radix i] at bound ⊢
  exact quote S.height point _ _ _ _ (2^k) bits₀ (v).groupWidth _ w _ age ambient blocks bw units word rows
    (orig.trans bound) (by rw [radix];exact Nat.two_pow_pos k)

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
