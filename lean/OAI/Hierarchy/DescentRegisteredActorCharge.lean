import OAI.Hierarchy.DescentRegisteredResetCharges
import OAI.Hierarchy.DescentResetSelectedActorInvoice

namespace OAI
/-! The registered reset opcode pays the actor selected from its own preceding date. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup
open ProtocolRAM
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule}
  {k D n deg C f g cutRate tail : ℕ} (rates : ResetRates G S k D n deg C f g cutRate tail)
  (i p h drift degree : ℕ) (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ)
  (prev : DatePorts) (floor w : ℕ)
local notation "codeRoom" => ScheduledCodeRoom G S rates.board k tail i p f g drift degree h ordinary op s Z
  prev.operandLanes prev.roleLanes prev.venue prev.io floor w prev.archive
local notation "A" => PhysicalReset.scheduled G S rates.board k tail i p f g drift degree h ordinary op s Z prev.operandLanes
  prev.roleLanes prev.venue prev.io.wire prev.io.roster floor
local notation "c" => S.groupWidth k tail i
local notation "bits₀" => S.localWalshBits p (c+k) f (quota S.rounds)

theorem actor_charge (space : codeRoom) (localRate receiver ratio saving lead exponent : ℕ)
    (degreeAt : prev.venue.degree=D) (Ceq : op.C=C)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (live : i<S.length) (hosts : 0<S.hostSize i)
    (localRoom : 8*bits₀≤h) (rootRoom : 8*(A).successor.groupWidth≤h)
    (blocks : 2^k≤TerminalScale.scale S.height localRate) (bw : bits₀≤TerminalScale.scale S.height localRate)
    (units : (A).successor.groupWidth≤TerminalScale.scale S.height receiver) (age : S.height≤Nat.log 2 h)
    (ambient : 2^h≤S.initialSites) (word : w≤ratio*h)
    (quote : ∀ J H groups stages copies N bits wid rows w fee : ℕ,
      J≤Nat.log 2 h → 2^h≤copies → N≤TerminalScale.scale J localRate → bits≤TerminalScale.scale J localRate →
      wid≤TerminalScale.scale J receiver → w≤ratio*h → rows*h≤(2+N)*h+groups*(32*N*bits+16*wid) →
      fee≤(ActorSetup.actorLead (2^n) deg D (GroupStage.depthBound D n f g)*TerminalScale.scale J (4*localRate))*
        ResetOutput.receiptArea h H rows → 1≤ stages →
      fee*w≤H*h*(lead*TerminalScale.scale J exponent)+H*(groups*stages)*(lead*TerminalScale.scale J exponent)+copies/(2^J)^saving) :
    (resetCharges G S rates.board k tail i p f g drift degree h ordinary op s Z prev floor w space).actor ≤
      S.hostSize i*h*(lead*TerminalScale.scale S.height exponent)+S.hostSize i*(S.groupCount i*S.radix)*
        (lead*TerminalScale.scale S.height exponent)+S.initialSites/(2^S.height)^saving := by
  subst C
  let u := innerResetInputs G S rates.board k tail i p f g drift degree h ordinary op s Z prev floor w space
  have depth : u.roots.Ht=GroupStage.depthBound D n f g := by
    change GroupStage.depthBound prev.venue.degree n f g=_
    rw [degreeAt]
  exact NativePitch.selected_actor_invoice (i:=i) rates p h drift degree
    (NativePitch.incoming S k tail p f h ordinary (i+1)) op.w prev.operandLanes prev.roleLanes
    (DescentPrimitivePalette.printedBits G s Z op) prev.venue prev.io floor w localRate receiver ratio saving
    lead exponent u depth degreeAt baseGroups radix live hosts localRoom rootRoom blocks bw units age ambient word quote

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
