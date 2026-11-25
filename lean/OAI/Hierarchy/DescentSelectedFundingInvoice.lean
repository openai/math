import OAI.Hierarchy.DescentResetFundingCalendar
import OAI.Hierarchy.DescentResetSelectedRootRooms

namespace OAI
/-! Selected reset funding from true previous and current row volumes, measured independently. -/
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
local notation "L" a => TerminalScale.scale S.height a


local notation "st" => (v).funded
local notation "t" => (v).venue.census
local notation "root" => (v).finalEnd at₀

open PhysicalReset.FinalInputs

theorem selected_funding_invoice (w localRate ratio saving lead exponent : ℕ)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (live : i<S.length)
    (hosts : old.hosts=S.hostSize i) (groups : old.groups=S.groupCount i) (blocks : old.k=k)
    (localRoom : 8*bits₀≤h) (rootRoom : 8*(v).groupWidth≤h)
    (blockBound : 2^k≤L localRate) (walsh : bits₀≤L localRate) (units : (v).groupWidth≤L localRate)
    (dim : c₀+k≤L localRate) (sites : (t).jobs≤L localRate) (cap : old.cap≤L localRate)
    (prior : chunks old.groups old.lanes*h≤h+old.groups*(L localRate))
    (older : (st).oldLanes≤h) (current : (st).gatherLanes≤h)
    (prevWidth : (st).precision*(st).oldLanes≤h/2)
    (matrix : ((st).high+(st).low)*((st).high+(st).low)≤h/2)
    (packed : ((st).precision+(st).precision)*2^(st).low≤h/2)
    (join : DescentGLPacked.BankImage.SignedFields.joinWidth (st).precision (st).blocks*(st).gatherLanes≤h/2)
    (flag : (st).flagWidth≤h/2) (census : (t).width≤h/2)
    (age : S.height≤Nat.log 2 h) (ambient : 2^h≤S.initialSites) (word : w≤ratio*h)
    (quoted : ∀(J δ copies base W U : ℕ) (s : DescentFundedCensus.Setup) (shape : DescentFundedCensus.Shape),
      J≤Nat.log 2 h → 2^h≤copies → 1≤δ → W≤ratio*h → U≤TerminalScale.scale J (6+2*localRate) →
      fundingFactor s shape≤2000000*TerminalScale.scale J (2*localRate) →
      chunks s.oldGroups s.oldLanes*h≤U*h+s.oldGroups*U →
      chunks s.oldGroups s.gatherLanes*h≤U*h+s.oldGroups*U →
      2^s.high≤chunks s.oldGroups s.gatherLanes → shape.rows=s.hosts*chunks s.oldGroups s.gatherLanes →
      s.oldLanes≤h → s.gatherLanes≤h → s.precision*s.oldLanes≤h/2 →
      (s.high+s.low)*(s.high+s.low)≤h/2 → (s.precision+s.precision)*2^s.low≤h/2 →
      DescentGLPacked.BankImage.SignedFields.joinWidth s.precision s.blocks*s.gatherLanes≤h/2 →
      s.flagWidth≤h/2 → shape.width≤h/2 →
      (setupCharge s base W+fundedCharge shape s.capacity)*W≤
        s.hosts*h*(lead*TerminalScale.scale J exponent)+
          s.hosts*(s.oldGroups*δ)*(lead*TerminalScale.scale J exponent)+copies/(2^J)^saving) :
    (setupCharge (st) root w+fundedCharge (t) (st).capacity)*w≤
      S.hostSize i*h*(lead*L exponent)+S.hostSize i*(S.groupCount i*S.radix)*(lead*L exponent)+S.initialSites/(2^S.height)^saving:=by
  let U:=L localRate
  have one : 1≤U:=Nat.two_pow_pos _
  have sq:U≤U*U:=by simpa using Nat.mul_le_mul_right U one
  have big:1≤64*(U*U):=(one.trans sq).trans (Nat.le_mul_of_pos_left _ (by decide))
  have fees:U≤64*(U*U):=sq.trans (Nat.le_mul_of_pos_left _ (by decide))
  have sixty:64≤L 6:=Nat.pow_le_pow_right (by decide : 0<2) (show 6≤6*(S.height+1) by omega)
  have scale:64*(U*U)≤L (6+2*localRate):=by
    have x:=Nat.mul_le_mul_right (U*U) sixty
    simpa only [U,TerminalScale.scale_mul,two_mul] using x
  have q : old.groups=2^c₀:=groups.trans (S.group_power baseGroups radix i).symm
  have lower:e₀≤c₀:=by
    have next:=ResetOutput.next_difference S k tail i live
    exact bound₀.2.2.trans (by omega)
  let prev:=ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old
  have shape:=ResetOutput.funded_pitch G S rates.board k tail i p f g drift degree h e₀ cut₀ nextM C packet prev at₀ q lower
  have factor:=ResetOutput.funding_factor_local G S rates.board k tail i p f g drift degree h e₀ cut₀ nextM C packet prev
    at₀ S.height localRate lower (by change 2^old.k≤_;simpa only [blocks] using blockBound) dim sites cap
  have origin:=selected_root_rows rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old
    io.wire io.roster floor live localRoom rootRoom
  have z:=Nat.mul_le_mul blockBound walsh
  have short:(2+2^k)≤64*(U*U):=by nlinarith only [one,sq,blockBound]
  have bill:(32*2^k*bits₀+16*(v).groupWidth)≤64*(U*U):=by nlinarith only [units,sq,z]
  have oldPaid:chunks (st).oldGroups (st).oldLanes*h≤64*(U*U)*h+(st).oldGroups*(64*(U*U)):=by
    change chunks old.groups old.lanes*h≤_
    exact prior.trans (Nat.add_le_add (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right h big)
      (Nat.mul_le_mul_left old.groups fees))
  have newPaid:chunks (st).oldGroups (st).gatherLanes*h≤64*(U*U)*h+(st).oldGroups*(64*(U*U)):=by
    change chunks old.groups (2^e₀)*h≤64*(U*U)*h+old.groups*(64*(U*U))
    rw [q]
    exact origin.trans (Nat.add_le_add (Nat.mul_le_mul_right h short) (Nat.mul_le_mul_left _ bill))
  have out:=quoted S.height S.radix S.initialSites root w (64*(U*U)) (st) (t) age ambient
    (by rw [radix];exact Nat.two_pow_pos _) word scale factor oldPaid newPaid shape.1 shape.2
    older current prevWidth matrix packed join flag census
  change _≤old.hosts*h*_+old.hosts*(old.groups*S.radix)*_+_ at out
  rwa [hosts,groups] at out

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
