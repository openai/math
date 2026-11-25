import OAI.Hierarchy.DescentResetPrimitiveDatePrice
import OAI.Hierarchy.DescentResetSelectedReceipt
import OAI.Hierarchy.DescentPhysicalResetTailTariff

namespace OAI
/-! # The primitive price at the actually selected reset date and packed pitch -/
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
local notation "cost" => (v).birth.invoice+((v).primitive.clockBound (PhysicalReset.FinalInputs.originBudget (date₀))+
  7*(v).primitive.nameBound (PhysicalReset.FinalInputs.originBudget (date₀)))

theorem selected_primitive_invoice (w localRate receiver ratio saving lead exponent : ℕ)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (live : i<S.length)
    (localRoom : 8*bits₀≤h) (rootRoom : 8*(v).groupWidth≤h)
    (shape : ResetOutput.PrimitiveLimits (v) (TerminalScale.scale S.height localRate) inc 100)
    (blocks : 2^k≤TerminalScale.scale S.height localRate) (bw : bits₀≤TerminalScale.scale S.height localRate)
    (units : (v).groupWidth≤TerminalScale.scale S.height receiver)
    (age : S.height≤Nat.log 2 h) (ambient : 2^h≤S.initialSites) (word : w≤ratio*h)
    (quote : ∀j (z : ResetOutput) gain work H groups δ copies N b width rows w fee,
      j≤Nat.log 2 h→2^h≤copies→ResetOutput.PrimitiveLimits z (TerminalScale.scale j localRate) gain work→
      N≤TerminalScale.scale j localRate→b≤TerminalScale.scale j localRate→width≤TerminalScale.scale j receiver→w≤ratio*h→
      rows*h≤(2+N)*h+groups*(32*N*b+16*width)→
      fee≤z.primitiveFactor gain (z.primitiveWork work)*ResetOutput.receiptArea h H rows→1≤δ→
      fee*w≤H*h*(lead*TerminalScale.scale j exponent)+H*(groups*δ)*(lead*TerminalScale.scale j exponent)+copies/(2^j)^saving) :
    cost*w≤S.hostSize i*h*(lead*TerminalScale.scale S.height exponent)+
      S.hostSize i*(S.groupCount i*S.radix)*(lead*TerminalScale.scale S.height exponent)+S.initialSites/(2^S.height)^saving:=by
  have budget : PhysicalReset.FinalInputs.originBudget (date₀) = (v).primitiveWork 100 := by
    apply max_eq_right
    dsimp only [DescentPrimitiveBirth.Layout.argumentBudget]
    omega
  let issued := ResetOutput.fromBoard G S rates.board k tail i p f g drift degree h e₀ cut₀ (2^e₀)
    nextM C packet (ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old) at₀
  have output : (v) = issued := PhysicalReset.named_successor G S rates.board k tail i p f g drift degree h
    e₀ cut₀ (2^e₀) nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  have inv := PhysicalReset.selected_inventory G S rates.board k tail i p f g drift degree h cut₀
    nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  have eqn := selected_root_exponent (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes
    printedBits old io.wire io.roster floor
  have lookup (t : ℕ) (hit : t ∈ issued.rootUnits ∨ t ∈ issued.receiverUnits) :
      t * issued.receiver.lanes ≤ h/2 := by
    rw [← output] at hit ⊢
    rw [inv.2.2.1, ← eqn]
    exact (v).operand_room cut₀ cut₀ (S.groupWidth k tail (i+1)) h rootRoom hit
  have bound:=ResetOutput.primitive_volume G S rates.board k tail i p f g drift degree h e₀ cut₀ nextM C packet
    (ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old) at₀ ((v).primitiveWork 100)
    radix live lookup
  change issued.birth.invoice + (issued.primitive.clockBound ((v).primitiveWork 100) +
    7 * issued.primitive.nameBound ((v).primitiveWork 100)) ≤ issued.primitiveFactor inc ((v).primitiveWork 100) *
    ResetOutput.receiptArea h (S.hostSize i) (chunks (S.groupCount i) (2^e₀)) at bound
  rw [← output] at bound
  have rows:=selected_root_rows rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old
    io.wire io.roster floor live localRoom rootRoom
  change chunks (2^c₀) (v).middle.rootLanes*h ≤ _ at rows
  rw [inv.2.2.2] at rows
  rw [← S.group_power baseGroups radix i] at bound
  rw [budget,←S.group_power baseGroups radix i]
  exact quote S.height (v) inc 100 _ _ _ _ (2^k) bits₀ (v).groupWidth _ w _
    age ambient shape blocks bw units word rows bound
    (by rw [radix];exact Nat.two_pow_pos k)

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
