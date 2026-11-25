import OAI.Hierarchy.DescentResetActorScale
import OAI.Hierarchy.DescentResetSelectedRootRooms
import OAI.Hierarchy.DescentNamedResetDateInputs

namespace OAI
/-! The selected root pitch pays the real actor body on the original old hosts. -/
namespace Hierarchy.DescentDatedAddressBook.ActorSetup
open DescentCompiler DescentCompiler.TerminalScale Filter

theorem actor_date_price (Y d D T rate receiver ratio saving : ℕ) :
    ∃C exponent : ℕ,∀ᶠ h : ℕ in atTop,∀ J H groups stages copies N bits width rows w fee : ℕ,
      J≤Nat.log 2 h → 2^h≤copies → N≤ scale J rate → bits≤ scale J rate → width≤ scale J receiver →
      w≤ratio*h → rows*h≤(2+N)*h+groups*(32*N*bits+16*width) →
      fee≤(actorLead Y d D T*scale J (4*rate))*ResetOutput.receiptArea h H rows → 1≤ stages →
      fee*w≤H*h*(C*scale J exponent)+H*(groups*stages)*(C*scale J exponent)+copies/(2^J)^saving := by
  obtain ⟨C,exp,late⟩:=clipped_date_price (actorLead Y d D T) (4*rate) 3 rate receiver ratio saving
  refine ⟨C,exp,?_⟩
  filter_upwards [late] with h bound
  intro J H groups stages copies N bits width rows w fee age many cells cost field word traffic invoice last
  exact bound J H groups stages copies _ N bits width rows w fee age many le_rfl cells cost field word traffic invoice last

end Hierarchy.DescentDatedAddressBook.ActorSetup

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


private theorem actor_member (V : ResetOutput) : V.actor.unitBits ∈ V.rootUnits := by
  simp [ResetOutput.rootUnits]

set_option maxHeartbeats 800000 in
theorem selected_actor_invoice (w localRate receiver ratio saving lead exponent : ℕ)
    (u : (date₀).DateInputs ((date₀).stageStart floor) w)
    (depth : u.roots.Ht=GroupStage.depthBound D n f g) (degreeAt : old.degree=D)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (live : i<S.length) (hosts : 0<S.hostSize i)
    (localRoom : 8*bits₀≤h) (rootRoom : 8*(v).groupWidth≤h)
    (blocks : 2^k≤TerminalScale.scale S.height localRate) (bw : bits₀≤TerminalScale.scale S.height localRate)
    (units : (v).groupWidth≤TerminalScale.scale S.height receiver) (age : S.height≤Nat.log 2 h)
    (ambient : 2^h≤S.initialSites) (word : w≤ratio*h)
    (quote : ∀ J H groups stages copies N bits wid rows w fee : ℕ,
      J≤Nat.log 2 h → 2^h≤copies → N≤TerminalScale.scale J localRate → bits≤TerminalScale.scale J localRate →
      wid≤TerminalScale.scale J receiver → w≤ratio*h → rows*h≤(2+N)*h+groups*(32*N*bits+16*wid) →
      fee≤(ActorSetup.actorLead (2^n) h₀ D (GroupStage.depthBound D n f g)*TerminalScale.scale J (4*localRate))*
        ResetOutput.receiptArea h H rows → 1≤ stages →
      fee*w≤H*h*(lead*TerminalScale.scale J exponent)+H*(groups*stages)*(lead*TerminalScale.scale J exponent)+copies/(2^J)^saving) :
    ((v).actor.actorTicks u.actor ((v).middle.stop at₀) w+
      7*names ((v).actor.actorBody u.actor ((v).middle.stop at₀) w))*w ≤
      S.hostSize i*h*(lead*TerminalScale.scale S.height exponent)+S.hostSize i*(S.groupCount i*S.radix)*
        (lead*TerminalScale.scale S.height exponent)+S.initialSites/(2^S.height)^saving := by
  let V:=(v).actor
  let T:=GroupStage.depthBound D n f g
  have dfit : u.actor.degree=D := degreeAt
  have kfit : u.actor.treeCap=2^T := congrArg (2^·) depth
  have nativeJobs : V.shapes=(DescentDenseHostOrder.roster rates.board k T).card := by
    change (DescentDenseHostOrder.roster rates.board k (GroupStage.depthBound old.degree n f g)).card=_
    rw [degreeAt]
  have nativeArity : V.arity=DescentSharedBookScan.width k (2^n) D := by
    change DescentSharedBookScan.width k (2^n) old.degree=_; rw [degreeAt]
  have nativeCount : V.maxCount=D*2^T := by
    change old.degree*2^(GroupStage.depthBound old.degree n f g)=_; rw [degreeAt]
  have oldWidth : V.oldWidth≤TerminalScale.scale S.height localRate := by
    refine le_trans ?_ bw
    change c₀+k ≤ S.localWalshBits p (c₀+k) f (quota S.rounds)
    unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits
    omega
  have fee := V.factor_scale rates.board D T k S.height localRate nativeJobs nativeArity nativeCount oldWidth blocks
  have lanes : 0<V.lanes := Nat.two_pow_pos _
  have unitsPos : 0<V.unitBits := by
    change 0<(2*k+n+2)*2^k+_
    exact Nat.add_pos_left (Nat.mul_pos (by omega) (Nat.two_pow_pos _)) _
  have rootExponent := selected_root_exponent (i:=i) rates p h drift degree nextM packet oldLanes
    primitiveLanes printedBits old io.wire io.roster floor
  have fit : V.unitBits*V.lanes≤h/2 := by
    have physical : V.lanes = 2^e₀ := rfl
    rw [physical, ←rootExponent]
    exact (v).operand_room cut₀ cut₀ (S.groupWidth k tail (i+1)) h rootRoom (Or.inl (actor_member (v)))
  have paid := V.actor_price u.actor ((v).middle.stop at₀) w h hosts lanes unitsPos fit (by change 7≤7; exact le_rfl)
  rw [dfit,kfit] at paid
  have rows := selected_root_rows (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old
    io.wire io.roster floor live localRoom rootRoom
  rw [←S.group_power baseGroups radix i]
  exact quote S.height (S.hostSize i) (2^c₀) S.radix S.initialSites (2^k) bits₀ (v).groupWidth V.chunksPerHost
    w _ age ambient blocks bw units word rows (paid.trans (Nat.mul_le_mul_right _ fee))
      (by rw [radix]; exact Nat.two_pow_pos _)

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
