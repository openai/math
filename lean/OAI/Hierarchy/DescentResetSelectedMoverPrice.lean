import OAI.Hierarchy.DescentResetSelectedPrimitivePrice
import OAI.Hierarchy.DescentRetainedHomeMoverVolume

namespace OAI
/-! # A single registered prior-role move on the selected reset date -/
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

open DescentRetainedHomeMover DescentResetRetainedSetup DescentCompiler.TerminalScale Filter
local notation "z₀" => (v).roleTransfer
local notation "L" => (z₀).transfer
local notation "P₀" => (z₀).placement
local notation "U" => (v).retainedRoleUnit

theorem selected_mover_invoice (w priorUnit packetUnit successorUnit ratio coeff saving : ℕ)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (live : i<S.length)
    (ap : (z₀).pitches.Apertures h) (oldPos : 0<primitiveLanes)
    (oldDensity : S.groupCount i≤primitiveLanes ∨ h≤primitiveLanes*priorUnit)
    (packetDensity : S.groupCount (i+1)≤(z₀).rootLanes ∨ h≤(z₀).rootLanes*packetUnit)
    (newDensity : S.groupCount (i+1)≤(P₀).lanes ∨ h≤(P₀).lanes*successorUnit)
    (_late : S.height≤Nat.log 2 h) (ambient : 2^h≤S.initialSites) (word : w≤ratio*h)
    (units : (z₀).invoiceUnits*ratio≤ scale S.height coeff)
    (literal : 5*(h+1)^4*2^(coeff*(S.height+1))*2^(h/2)≤S.initialSites/(2^S.height)^saving) :
    (z₀).invoice ((v).fullEnd at₀) w*w≤
      S.hostSize i*h*((z₀).invoiceUnits*ratio*(z₀).pitches.hostRate inc)+
      S.hostSize i*S.groupCount i*((z₀).invoiceUnits*ratio*DescentRetainedSeven.Chart.fieldRate inc priorUnit U packetUnit successorUnit)+
      S.initialSites/(2^S.height)^saving:=by
  clear _late
  let rows:=S.groupCount (i+1)
  let H:=S.hostSize i
  let K:=(z₀).invoiceUnits*ratio
  have split:rows*2^k=S.groupCount i:=by
    simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (S.groupDigits live radix)).symm
  have groups:rows≤S.groupCount i:=(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)).trans_eq split
  have growth:S.hostSize (i+1)=H*inc:=by simp only [H,AtomSchedule.hostSize,pow_succ,Nat.mul_assoc]
  have pitch:(L).CalendarPitch c₀ k h U:=⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have names:(L).groups=2^c₀:=(S.group_power baseGroups radix i).symm
  have sitesPos:0<S.initialSites:=(Nat.two_pow_pos h).trans_le ambient
  have hostPos:0<H:=by
    dsimp [H,AtomSchedule.hostSize]
    rw [radix]
    positivity
  have used:0<U:=by exact Nat.le_max_left 1 _
  have window:S.groupCount i≤(z₀).rootLanes*(P₀).blocks ∨ h≤(z₀).rootLanes*packetUnit:=by
    rcases packetDensity with low|high
    · exact Or.inl (split.symm.le.trans (Nat.mul_le_mul_right _ low))
    · exact Or.inr high
  have cost:=(z₀).native_invoice ((v).fullEnd at₀) w h c₀ k U priorUnit packetUnit successorUnit ratio ap
    pitch names hostPos used oldPos oldDensity rfl split window newDensity word
  have pack : (z₀).pitches.rowBits h priorUnit U packetUnit successorUnit ≤
      H*h*(z₀).pitches.hostRate inc+H*S.groupCount i*DescentRetainedSeven.Chart.fieldRate inc priorUnit U packetUnit successorUnit+
      5*(h+1)^4*2^(h/2) := (z₀).pitches.row_invoice h inc priorUnit U packetUnit successorUnit growth.le groups
  have book:K*(5*(h+1)^4*2^(h/2))≤S.initialSites/(2^S.height)^saving:=calc
    _≤ scale S.height coeff*(5*(h+1)^4*2^(h/2)):=Nat.mul_le_mul_right _ units
    _=5*(h+1)^4*2^(coeff*(S.height+1))*2^(h/2):=by unfold TerminalScale.scale;ring
    _≤_:=literal
  exact cost.trans ((Nat.mul_le_mul_left K pack).trans (by
    calc
      _=H*h*(K*(z₀).pitches.hostRate inc)+H*S.groupCount i*(K*DescentRetainedSeven.Chart.fieldRate inc priorUnit U packetUnit successorUnit)+
          K*(5*(h+1)^4*2^(h/2)):=by ring
      _≤_:=Nat.add_le_add_left book _))

theorem selected_mover_literal (coeff saving : ℕ) :
    ∀ᶠ h:ℕ in Filter.atTop,∀J copies,J≤Nat.log 2 h→2^h≤copies→
      5*(h+1)^4*2^(coeff*(J+1))*2^(h/2)≤copies/(2^J)^saving:=by
  filter_upwards [DescentCompiler.global_control_shared 5 4 coeff 1 saving] with h room
  intro J copies late size
  exact room J (coeff*(J+1)) copies late (by simp) size

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
