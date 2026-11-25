import OAI.Hierarchy.DescentResetCompactTrunkPrice
import OAI.Hierarchy.DescentResetSelectedRootRooms
import OAI.Hierarchy.DescentDatedOperandHeader

namespace OAI
/-! The three compact trunk tables on the concrete selected reset calendar. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentDatedAddressBook DescentSIMDLookup DescentPackedWalsh
open ProtocolRAM
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
local notation "v" => (date₀).successor
local notation "at₀" => (date₀).rebased ((date₀).stageStart floor)
theorem selected_compact_trunk_invoice (w rate receiver ratio saving lead exponent : ℕ)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (live : i < S.length)
    (localRoom : 8*bits₀ ≤ h) (rootRoom : 8*(v).groupWidth ≤ h)
    (blocks : 2^k ≤ TerminalScale.scale S.height rate) (bw : bits₀ ≤ TerminalScale.scale S.height rate)
    (increase : 2^S.hostGain*S.radix ≤ TerminalScale.scale S.height rate)
    (units : (v).groupWidth ≤ TerminalScale.scale S.height receiver)
    (age : S.height ≤ Nat.log 2 h) (ambient : 2^h ≤ S.initialSites) (word : w ≤ ratio*h)
    (quote : ∀J H groups stages copies factor N b width rows w fee : ℕ,
      J ≤ Nat.log 2 h → 2^h ≤ copies → factor ≤ 32768*TerminalScale.scale J rate →
      N ≤ TerminalScale.scale J rate → b ≤ TerminalScale.scale J rate → width ≤ TerminalScale.scale J receiver →
      w ≤ ratio*h → rows*h ≤ (2+N)*h+groups*(32*N*b+16*width) →
      fee ≤ factor*(H+H*rows+(h+1)^0*2^(h/2)) → 1 ≤ stages →
      fee*w ≤ H*h*(lead*TerminalScale.scale J exponent)+H*(groups*stages)*(lead*TerminalScale.scale J exponent)+copies/(2^J)^saving) :
    (v).front.compactTrunkWords*w ≤ S.hostSize i*h*(lead*TerminalScale.scale S.height exponent)+
      S.hostSize i*(S.groupCount i*S.radix)*(lead*TerminalScale.scale S.height exponent)+S.initialSites/(2^S.height)^saving := by
  let previous := ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old
  let out := ResetOutput.fromBoard G S rates.board k tail i p f g drift degree h e₀ cut₀
    (2^e₀) nextM C packet previous at₀
  have same : (v)=out := PhysicalReset.named_successor G S rates.board k tail i p f g drift degree h
    e₀ cut₀ (2^e₀) nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  have exponent := selected_root_exponent (i:=i) rates p h drift degree nextM packet oldLanes
    primitiveLanes printedBits old io.wire io.roster floor
  have bought (x : ℕ) (hx : x∈out.receiverUnits) : x*2^e₀≤h/2 := by
    rw [←same] at hx
    have small := (v).operand_room cut₀ cut₀ (S.groupWidth k tail (i+1)) h rootRoom (Or.inr hx)
    rwa [exponent] at small
  have allocated := ResetOutput.compact_trunk_volume G S rates.board k tail i p f g drift degree h e₀ cut₀ nextM C packet
    previous at₀ rate live radix bought increase
  change out.front.compactTrunkWords ≤ (32768*TerminalScale.scale S.height rate)*
    (S.hostSize i+S.hostSize i*chunks (S.groupCount i) (2^e₀)+2^(h/2)) at allocated
  rw [←same] at allocated
  have rows:=selected_root_rows (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old
    io.wire io.roster floor live localRoom rootRoom
  have groupEq : (v).middle.rootGroups = S.groupCount i := by
    change 2^c₀ = S.groupCount i
    exact S.group_power baseGroups radix i
  have inv := PhysicalReset.selected_inventory G S rates.board k tail i p f g drift degree h
    cut₀ nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  rw [groupEq,inv.2.2.2,S.group_power baseGroups radix i] at rows
  exact quote S.height _ _ _ _ _ (2^k) bits₀ (v).groupWidth _ w _ age ambient le_rfl blocks bw units word rows
    (by simpa only [pow_zero,one_mul] using allocated) (by rw [radix];exact Nat.two_pow_pos k)

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
