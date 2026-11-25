import OAI.Hierarchy.DescentScheduledPrimaryDonorWords
import OAI.Hierarchy.DescentAcquiredPrimaryDonors
import OAI.Hierarchy.DescentCalendarPrimarySpans

namespace OAI
/-! # The actual reset operand panels provide every primary donor register -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
open DescentSixParty.Chronology DescentSIMDLookup DescentWalshPrecision DescentSixParty.PackedFlow.Padded ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open scoped Classical Fin.CommRing
set_option maxHeartbeats 750000
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ)
    (ports : Chronology.DatePorts)
local notation "old" => ports.venue
local notation "io" => ports.io

local notation "a" => scheduledAtPorts G S board k tail age p f gain drift degree h ordinary op s Z ports
variable (floor w : ℕ)
local notation "ap" => (a) floor
local notation "post" => ports.afterPad k floor
local notation "next" => ports.priorStart k floor
local notation "pack" => ports.resetPad k
local notation "L" => (ap).inner.successor.setup.retained
local notation "support" => ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
  ports.operandLanes ports.roleLanes old io next w (post).archive

local notation "raw" => previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor

open DescentOrdinaryHostPad
variable {V : Type} {dimU : ℕ} {bits : V→ℕ} {U : MarkedWorld F dimU V bits}
    {q ε : ℝ} {z D wire hist : ℕ}
local notation "loaded" => ({raw with hosts:=(old).hosts} : DescentResetRetainedSetup.Layout)

open DescentRetainedRangeDigits DescentDatedPriorOperand DescentLocalArchiveOrder DescentKernelHistory
open DescentGL DescentColonies DescentPackedColony DescentSixParty.PackedFlow.Channels
variable (data : Fin (pack).dataRect.pages→Fin ports.operandHosts→Fin (old).groups→Cell (ports.operandBits*ports.nodes))
    (roles : Fin (2^k)→Fin ports.operandHosts→Fin (old).groups→Cell (ports.tokenBits*ports.nodes))
local notation "X" => padValues G S board k tail age p f gain drift degree h ordinary op s Z ports floor data roles
local notation "l" => loaded
open DescentSixParty.ClosedReset.Window DescentRelativeContacts DescentFallbackShapeTable DescentResetHostSize
open DescentKernelHistory DescentBundleHistory DescentPrimitivePalette DescentResetLocalNodes
variable (supportAt:support) (homes : (old).hosts=S.hostSize age) (blocks : (old).k=k)
    (groups : (old).groups=S.groupCount age) (widths : DatePorts.ArchiveWidths G S op ports k tail p drift degree h age)
    (args : ports.argumentsPerNode=(if age=0 then 3*(S.firstWidth G.b p/p) else S.retainedArgumentsAt G drift))
variable {n₀ h₀ C₀ cut₀ : ℕ} {input : Reached U G q ε S k age z D wire hist}
    {ctl : ResetRates G S k D n₀ h₀ C₀ f gain cut₀ tail} (closed_ : ClosedReset input ctl)
    (oldA : Archive U) (number : Local oldA.bit) (room : DatePorts.RangeRoom ports input oldA.bit)
    {R : ℕ} (spec : WorldShape p R oldA.bit) (hp : 0<p) (pin : V→ℕ)
    (label : NodeOrder.All oldA.bit→Label G s Z op) (flags : Fin (2^(old).k)→Fin ports.nodes→Fin ports.operandHosts→Fin (old).groups→ℕ)
    (mem : Memory w)
local notation "pointer_" => Reached.argumentPointer input oldA.bit number spec hp pin ports.argumentsPerNode
local notation "archive_" => DatePorts.ArchiveRead ports input oldA.bit number room spec op label pointer_ flags mem
local notation "scheduled_" => ScheduledOldAt G S board k tail age p f gain drift degree h ordinary op s Z ports floor w
  supportAt input mem homes blocks groups widths args number room spec label data roles
variable (archive : archive_) (stored : scheduled_) (sized : ports.RoleRows)
    (alphabet : ports.tokenBits=printedBits G s Z op) (rolePos : 0<ports.roleLanes)
    (roleRoom : ports.tokenBits*ports.nodes*ports.roleLanes≤w)
    (width : ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (pop : Fintype.card input.V≤ports.operandHosts) (positive : 0<ports.operandBits)
    (fits : ports.argumentsPerNode<2^ports.operandBits)
local notation "T" => closed_.terminals
local notation "cc" => (T).commonDepth
local notation "wide" => S.groupWidth k tail age+k
local notation "same_" => scheduled_loaded G S board k tail age p f gain drift degree h ordinary op s Z ports floor
  widths homes groups args
local notation "realChart" => (ap).inner.successor.setup

include archive stored sized alphabet rolePos roleRoom width pop positive fits in
private theorem acquired_donor_read (c : DescentResetOperandSetup.Chart) (same : (l)=c.retained)
    (total:c.retained.high+c.retained.low=wide) (axis:c.retained.cut=cc) (blockSize:c.retained.blocks=2^k)
    (groupSize:c.retained.groups=S.groupCount age) (span:2^(c.retained.high+c.retained.low)=c.retained.groups*c.retained.blocks)
    (cutRoom:c.retained.cut≤c.retained.high+c.retained.low) (hostRoom:Fintype.card input.V≤c.retained.hosts)
    (nodeRoom:∀v,Fintype.card (oldA.bit.recipe v).Node≤c.retained.previousNodes)
    (budget:∀v n₁,((spec.sites v).recipe hp).arity n₁≤c.retained.previousArgs)
    (basis:DescentGL.Layout (c.retained.high+c.retained.low)) (won:HEq basis closed_.frame.basis) :
    PrimaryDonorRead closed_ c oldA number spec hp pin total axis blockSize groupSize span cutRoom hostRoom
      nodeRoom budget basis (same ▸ (X)):=by
  cases c with
  | mk bucket placement packets casts oldDegree oldCap oldPieces signedBits signedLanes ticketBits fieldBits queryBits rotorBits fallbackBits fallbackInputs =>
    change (l)=bucket at same
    subst bucket
    let chart_ : DescentResetOperandSetup.Chart:=⟨(l),placement,packets,casts,oldDegree,oldCap,oldPieces,
      signedBits,signedLanes,ticketBits,fieldBits,queryBits,rotorBits,fallbackBits,fallbackInputs⟩
    intro y
    let t:=(T).home y.1
    let carrier:=(input.vertex.trans (Fin.castLEEmb hostRoom)) (closed_.frame.host.symm ((T).code t).1)
    let hi:=(closed_.reset.rootBlock (T) (.inr t)).cast (congrArg (2^·) axis).symm
    let dirs:=finCongr (congrArg (fun s=>2^s) (congrArg₂ Nat.sub total axis))
    let donor:=calendar_donor_index (b:=closed_) («a»:=oldA) (yy:=y) (chart:=chart_) (total:=total) (axis:=axis)
    have donorFields:=named_primary_donor_words (G:=G) (S:=S) (board:=board) (k:=k) (tail:=tail) (age:=age)
      (p:=p) (f:=f) (gain:=gain) (drift:=drift) (degree:=degree) (h:=h) (ordinary:=ordinary) (op:=op)
      (s:=s) (Z:=Z) (ports:=ports) (floor:=floor) (w:=w) (data:=data) (roles:=roles)
      (size:=span) (cut:=cutRoom) (matrix:=basis) (carrier:=carrier) (hi:=hi)
      (room:=room) (archive:=archive) (site:=fun u:DescentNamedContact.Fibre (T).home t=>u.val)
      (donors:=fun u=>donor u) (hp:=hp) (priorArgs:=fun u n₁=>budget u.val n₁)
      (sameRows:=fun u=>calendar_donor_place (b:=closed_) (chart:=chart_) (total:=total) (axis:=axis)
        (blocks:=blockSize) (groups:=groupSize) (size:=span) (fits:=cutRoom) («L»:=basis) (won:=won)
        (room:=hostRoom) (t:=t) u)
      (width:=width) (fits:=fits) (sized:=sized) (alphabet:=alphabet) (rolePos:=rolePos)
      (roleRoom:=roleRoom) (pop:=pop) (top:=hostRoom) (positive:=positive) (stored:=stored)
    exact ⟨fun lo=>donorFields.1 (dirs.symm lo),donorFields.2.1,fun u s₀ f₀=>donorFields.2.2.1 u s₀.1 s₀.2 f₀,
      fun u s₀ f₀=>donorFields.2.2.2 u s₀.1 s₀.2 f₀⟩

include archive stored sized alphabet rolePos roleRoom width pop positive fits in
theorem scheduled_primary_donor_read
    (total:(L).high+(L).low=wide) (axis:(L).cut=cc) (blockSize:(L).blocks=2^k)
    (groupSize:(L).groups=S.groupCount age) (span:2^((L).high+(L).low)=(L).groups*(L).blocks)
    (cutRoom:(L).cut≤(L).high+(L).low) (hostRoom:Fintype.card input.V≤(L).hosts)
    (nodeRoom:∀v,Fintype.card (oldA.bit.recipe v).Node≤(L).previousNodes)
    (budget:∀v n₁,((spec.sites v).recipe hp).arity n₁≤(L).previousArgs)
    (basis:DescentGL.Layout ((L).high+(L).low)) (won:HEq basis closed_.frame.basis) :
    PrimaryDonorRead closed_ (realChart) oldA number spec hp pin total axis blockSize groupSize span cutRoom
      hostRoom nodeRoom budget basis ((same_) ▸ (X)):=by
  exact acquired_donor_read (archive:=archive) (stored:=stored) (sized:=sized) (alphabet:=alphabet)
    (rolePos:=rolePos) (roleRoom:=roleRoom) (width:=width) (pop:=pop) (positive:=positive) (fits:=fits)
    (G:=G) (S:=S) (board:=board) (k:=k) (tail:=tail) (age:=age) (p:=p) (f:=f) (gain:=gain)
    (drift:=drift) (degree:=degree) (h:=h) (ordinary:=ordinary) (op:=op) (s:=s) (Z:=Z)
    (ports:=ports) (floor:=floor) (w:=w) (data:=data) (roles:=roles) (closed_:=closed_) (oldA:=oldA)
    (number:=number) (room:=room) (spec:=spec) (hp:=hp) (pin:=pin)
    (c:=realChart) (same:=same_) (total:=total) (axis:=axis) (blockSize:=blockSize) (groupSize:=groupSize)
    (span:=span) (cutRoom:=cutRoom) (hostRoom:=hostRoom) (nodeRoom:=nodeRoom) (budget:=budget)
    (basis:=basis) (won:=won)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
