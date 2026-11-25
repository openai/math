import OAI.Hierarchy.DescentScheduledPrimaryDonorWords
import OAI.Hierarchy.DescentScheduledPrimaryDonorRead
import OAI.Hierarchy.DescentCalendarPrimarySpans

namespace OAI
/-! # The actual reset operand panels provide every primary donor register -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open scoped Classical Fin.CommRing
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
open DescentSixParty.Chronology DescentSIMDLookup DescentWalshPrecision DescentSixParty.PackedFlow.Padded ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ)
    (ports : Chronology.DatePorts)
local notation "old" => ports.venue

local notation "scheduledDate" => scheduledAtPorts G S board k tail age p f gain drift degree h ordinary op s Z ports
variable (floor w : ℕ)
local notation "ap" => (scheduledDate) floor
local notation "pack" => ports.resetPad k
local notation "L" => (ap).inner.successor.setup.retained

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
local notation "loadedLayout" => loaded
open DescentSixParty.ClosedReset.Window DescentRelativeContacts DescentFallbackShapeTable DescentResetHostSize
open DescentKernelHistory DescentBundleHistory DescentPrimitivePalette DescentResetLocalNodes
variable (supportAt : ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
  ports.operandLanes ports.roleLanes ports.venue ports.io (ports.priorStart k floor) w (ports.afterPad k floor).archive) (homes : (old).hosts=S.hostSize age) (blocks : (old).k=k)
    (groups : (old).groups=S.groupCount age) (widths : DatePorts.ArchiveWidths G S op ports k tail p drift degree h age)
    (args : ports.argumentsPerNode=(if age=0 then 3*(S.firstWidth G.b p/p) else S.retainedArgumentsAt G drift))
variable {n₀ h₀ C₀ cut₀ : ℕ} {input : Reached U G q ε S k age z D wire hist}
    {ctl : ResetRates G S k D n₀ h₀ C₀ f gain cut₀ tail} (closed_ : ClosedReset input ctl)
    (oldA : Archive U) (number : Local oldA.bit) (room : DatePorts.RangeRoom ports input oldA.bit)
    {R : ℕ} (spec : WorldShape p R oldA.bit) (hp : 0<p) (pin : V→ℕ)
    (label : NodeOrder.All oldA.bit→Label G s Z op) (flags : Fin (2^(old).k)→Fin ports.nodes→Fin ports.operandHosts→Fin (old).groups→ℕ)
    (mem : Memory w)
local notation "pointer_" => Reached.argumentPointer input oldA.bit number spec hp pin ports.argumentsPerNode
variable (archive : DatePorts.ArchiveRead ports input oldA.bit number room spec op label
    (Reached.argumentPointer input oldA.bit number spec hp pin ports.argumentsPerNode) flags mem)
    (stored : ScheduledOldAt G S board k tail age p f gain drift degree h ordinary op s Z ports floor w
      supportAt input mem homes blocks groups widths args number room spec label data roles) (sized : ports.RoleRows)
    (alphabet : ports.tokenBits=printedBits G s Z op) (rolePos : 0<ports.roleLanes)
    (roleRoom : ports.tokenBits*ports.nodes*ports.roleLanes≤w)
    (width : ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (pop : Fintype.card input.V≤ports.operandHosts) (positive : 0<ports.operandBits)
    (fits : ports.argumentsPerNode<2^ports.operandBits)
local notation "same_" => scheduled_loaded G S board k tail age p f gain drift degree h ordinary op s Z ports floor
  widths homes groups args

section Counts
variable {G S k age oldA}

/-- Population in every physical root cell, including roots with no archived node. -/
def OriginalRootCounts (layout:DescentResetRetainedSetup.Layout) (values:layout.Values)
    (size:2^(layout.high+layout.low)=layout.groups*layout.blocks) (cutRoom:layout.cut≤layout.high+layout.low)
    (basis:DescentGL.Layout (layout.high+layout.low)) (hostRoom:Fintype.card input.V≤layout.hosts)
    (groupSize:layout.groups=S.groupCount age) (blockSize:layout.blocks=2^k) : Prop:=
  ∀(carrier:Fin layout.hosts)(hi:Block layout.cut)(d₀:Fin layout.donors),
    let source:=(rearrange basis).symm (DescentIssuedFallbackPanel.join cutRoom hi d₀)
    let coords:Fin layout.groups×Fin layout.blocks:=finProdFinEquiv.symm (source.cast size)
    let words:=layout.site (fun j=>blockValues cutRoom (layout.before size values j) basis) carrier hi
    layout.originalCount words d₀=∑v,if DescentPaidResidentCount.occupies input.placement (Equiv.refl _)
      (input.vertex.trans (Fin.castLEEmb hostRoom)) carrier (coords.1.cast groupSize) (coords.2.cast blockSize) v
      then Fintype.card (oldA.bit.recipe v).Node else 0

end Counts

include archive stored sized alphabet rolePos roleRoom pop positive in
private theorem loaded_root_counts (layout:DescentResetRetainedSetup.Layout) (same:(loadedLayout)=layout)
    (size:2^(layout.high+layout.low)=layout.groups*layout.blocks) (cutRoom:layout.cut≤layout.high+layout.low)
    (basis:DescentGL.Layout (layout.high+layout.low)) (hostRoom:Fintype.card input.V≤layout.hosts)
    (groupSize:layout.groups=S.groupCount age) (blockSize:layout.blocks=2^k) :
    OriginalRootCounts (input:=input) (oldA:=oldA) layout (same ▸ (X)) size cutRoom basis hostRoom groupSize blockSize:=by
  subst layout
  intro carrier hi d₀
  obtain ⟨_,loadedRoles,_,_,_,_⟩:=stored
  exact registered_original_count (G:=G) (S:=S) (board:=board) (k:=k) (tail:=tail) (age:=age)
    (p:=p) (f:=f) (gain:=gain) (drift:=drift) (degree:=degree) (h:=h) (ordinary:=ordinary) (op:=op)
    (s:=s) (Z:=Z) (ports:=ports) (floor:=floor) (w:=w) (r₀:=input) (B:=oldA.bit) (number:=number) (data:=data) (roles:=roles)
    (size:=size) (cut:=cutRoom) (matrix:=basis) (carrier:=carrier) (hi:=hi) (d₀:=d₀)
    (population:=pop) (topHosts:=hostRoom) room spec label pointer_ flags mem archive sized alphabet
    rolePos roleRoom (fun x=>(loadedRoles x).2) positive

set_option maxHeartbeats 650000 in
include archive stored sized alphabet rolePos roleRoom pop positive in
theorem scheduled_root_counts (size:2^((L).high+(L).low)=(L).groups*(L).blocks)
    (cutRoom:(L).cut≤(L).high+(L).low) (basis:DescentGL.Layout ((L).high+(L).low))
    (hostRoom:Fintype.card input.V≤(L).hosts) (groupSize:(L).groups=S.groupCount age)
    (blockSize:(L).blocks=2^k) :
    OriginalRootCounts (input:=input) (oldA:=oldA) (L) ((same_) ▸ (X)) size cutRoom basis hostRoom groupSize blockSize:=
  loaded_root_counts (G:=G) (S:=S) (board:=board) (k:=k) (tail:=tail) (age:=age)
    (p:=p) (f:=f) (gain:=gain) (drift:=drift) (degree:=degree) (h:=h) (ordinary:=ordinary)
    (op:=op) (s:=s) (Z:=Z) (ports:=ports) (floor:=floor) (w:=w)
    (data:=data) (roles:=roles) (supportAt:=supportAt) (homes:=homes) (blocks:=blocks)
    (groups:=groups) (widths:=widths) (args:=args) (input:=input) (oldA:=oldA)
    (number:=number) (room:=room) (spec:=spec) (hp:=hp) (pin:=pin) (label:=label)
    (flags:=flags) (mem:=mem) (archive:=archive) (stored:=stored) (sized:=sized) (alphabet:=alphabet)
    (rolePos:=rolePos) (roleRoom:=roleRoom) (pop:=pop) (positive:=positive)
    (L) (same_) size cutRoom basis hostRoom groupSize blockSize

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
