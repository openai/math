import OAI.Hierarchy.DescentScheduledPaddedPages
import OAI.Hierarchy.DescentScheduledArchiveFormat
import OAI.Hierarchy.DescentRegisteredResetStep
import OAI.Hierarchy.DescentArchivePadInputs
import OAI.Hierarchy.DescentResetPriorFieldCases
import OAI.Hierarchy.DescentResetOperandMovedSources

namespace OAI
/-! # The original archive supplies every retained input of the scheduled venue movement -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentPackedColony DescentBundleHistory DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
open DescentSixParty.Chronology DescentSIMDLookup DescentWalshPrecision DescentSixParty.PackedFlow.Padded ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing
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
local notation "cap" => ((capCalendar G.b S.rounds gain S.height).take age).prod*256
local notation "support" => ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
  ports.operandLanes ports.roleLanes old io next w (post).archive

local notation "raw" => previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor

local notation "publisher" => priorArchivePhase G S board k tail age p f gain drift degree h ordinary op s Z ports floor w

open DescentOrdinaryHostPad DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
variable {V : Type} {width : ℕ} {bits : V→ℕ} {U : MarkedWorld F width V bits}
    {q ε : ℝ} {z D wire hist : ℕ}
local notation "loaded" => ({raw with hosts:=(old).hosts} : DescentResetRetainedSetup.Layout)

local notation "entry" sp => DatePorts.resetInputs G S board k tail age p f gain drift degree h ordinary op s Z ports floor w sp

private theorem retypePages {sourceLayout targetLayout : DescentResetRetainedSetup.Layout} (same : sourceLayout=targetLayout)
    (archive : PriorResetArchive) {top : ℕ} (mem : Memory w) (pages : sourceLayout.Values)
    (issued : ∀j,(archive.prior sourceLayout j).Fits w top ∧ sourceLayout.hosts*chunks sourceLayout.groups sourceLayout.previousLanes≤(archive.prior sourceLayout j).size ∧
      Reads (archive.prior sourceLayout j) (pages j) sourceLayout.previousLanes mem) :
    ∀j,(archive.prior targetLayout j).Fits w top ∧ targetLayout.hosts*chunks targetLayout.groups targetLayout.previousLanes≤(archive.prior targetLayout j).size ∧
      Reads (archive.prior targetLayout j) ((same ▸ pages : targetLayout.Values) j) targetLayout.previousLanes mem:=by
  subst targetLayout
  exact issued

theorem scheduled_venue_old (supportAt : support) (r : Reached U G q ε S k age z D wire hist) (m : Memory w)
    (seen : ports.held r floor m) (count : ports.archive.count.base<floor) (wires : ports.WireRoom w floor)
    (blocks : (old).k=k) (capDate : (old).cap=r.placement.cap) (groups : (old).groups=S.groupCount age)
    (native : ports.archive.Fits raw floor) (roleBlocks : 2^k≤ports.archive.roles.blocks)
    (roleLimit : ports.archive.roles.endAddress≤floor) (room : next<2^w)
    (live : 0<ports.roleLanes) (data : Fin (pack).dataRect.pages→Fin ports.operandHosts→Fin (old).groups→Cell (ports.operandBits*ports.nodes))
    (roles : Fin (2^k)→Fin ports.operandHosts→Fin (old).groups→Cell (ports.tokenBits*ports.nodes))
    (stored : ∀j,ports.operandHosts*chunks (old).groups ports.operandLanes≤(ports.archive.prior raw j).size ∧
      Reads (ports.archive.prior raw j) (data j) ports.operandLanes m)
    (tokens : ∀j,ports.operandHosts*chunks (old).groups ports.roleLanes≤(ports.archive.roles.bank j.val).size ∧
      Reads (ports.archive.roles.bank j.val) (roles j) ports.roleLanes m)
    (widths : DatePorts.ArchiveWidths G S op ports k tail p drift degree h age)
    (homes : (old).hosts=S.hostSize age)
    (args : ports.argumentsPerNode=(if age=0 then 3*(S.firstWidth G.b p/p) else S.retainedArgumentsAt G drift)) :
    let same:=scheduled_loaded G S board k tail age p f gain drift degree h ordinary op s Z ports floor widths homes groups args
    let pages : (L).Values:=same ▸ padValues G S board k tail age p f gain drift degree h ordinary op s Z ports floor data roles
    ∀j,((entry supportAt).bank.old j).Fits w next ∧ (L).hosts*chunks (L).groups (L).previousLanes≤((entry supportAt).bank.old j).size ∧
      Reads ((entry supportAt).bank.old j) (pages j) (L).previousLanes ((publisher).image m):=by
  let same:=scheduled_loaded G S board k tail age p f gain drift degree h ordinary op s Z ports floor widths homes groups args
  have measured:=scheduled_pad_pages G S board k tail age p f gain drift degree h ordinary op s Z ports floor w r m
    seen count wires blocks capDate groups native roleBlocks roleLimit room live data roles stored tokens
  exact retypePages (w:=w) same (post).archive ((publisher).image m) _ measured

/-- The previous register words together with their physical interpretation and their padded reset inputs. -/
abbrev ScheduledOldAt (supportAt : support) (r : Reached U G q ε S k age z D wire hist)
    (m : Memory w) (homes : (old).hosts=S.hostSize age) (blocks : (old).k=k)
    (groups : (old).groups=S.groupCount age)
    (widths : DatePorts.ArchiveWidths G S op ports k tail p drift degree h age)
    (args : ports.argumentsPerNode=(if age=0 then 3*(S.firstWidth G.b p/p) else S.retainedArgumentsAt G drift))
    {B : BitDescription U} (number : Local B) (bounds : DatePorts.RangeRoom ports r B)
    {R : ℕ} (shape : WorldShape p R B) (label : NodeOrder.All B→Label G s Z op)
    (data : (raw).Values) (roles : Fin (2^k)→Fin ports.operandHosts→Fin (old).groups→Cell (ports.tokenBits*ports.nodes)) : Prop :=
      (∀j,ports.operandHosts*chunks (old).groups ports.operandLanes≤(ports.archive.prior raw j).size ∧
        Reads (ports.archive.prior raw j) (data j) ports.operandLanes m) ∧
      (∀x,ports.operandHosts*chunks (old).groups ports.roleLanes≤(ports.archive.roles.bank x.val).size ∧
        Reads (ports.archive.roles.bank x.val) (roles x) ports.roleLanes m) ∧
      (∀x h₀ g₀,(roles x h₀ g₀).val=(encode (printedBits G s Z op) ports.nodes (fun j=>
        (DatePorts.slotAt ports r B number bounds (x.cast (congrArg (2^·) blocks.symm)) j h₀ g₀).elim 0
          (fun y=>token G s Z op (label y)))).val) ∧
      (∀x,data ((raw).sourceID (raw).arityField x)=fun h₀ g₀=>encode ports.operandBits ports.nodes (fun j=>
        ((DatePorts.slotAt ports r B number bounds (x.cast (congrArg (2^·) blocks.symm)) j h₀ g₀).elim 0
          (fun y=>(DescentRetainedRangeDigits.occurrences (shape.sites y.1) y.2).length):Cell ports.operandBits))) ∧
      (∀f j x,Reads (DescentDatedPriorOperand.previousBank ports.rangeLayout ports.archive.arguments
        (x.cast (congrArg (2^·) blocks.symm)) (page f j))
        (data ((raw).sourceID ((raw).operandField f j) x)) ports.operandLanes m) ∧
      let same:=scheduled_loaded G S board k tail age p f gain drift degree h ordinary op s Z ports floor widths homes groups args
      let pages : (L).Values:=same ▸ padValues G S board k tail age p f gain drift degree h ordinary op s Z ports floor data roles
      ∀j,((entry supportAt).bank.old j).Fits w next ∧ (L).hosts*chunks (L).groups (L).previousLanes≤((entry supportAt).bank.old j).size ∧
        Reads ((entry supportAt).bank.old j) (pages j) (L).previousLanes ((publisher).image m)

/-- Derive the complete old-data input of the original reset from the actual
chronological archive. The same source words feed both the dated native movement
and its old-node arity and occupation interpretation. -/
theorem scheduled_venue_archive_witness (supportAt : support) (r : Reached U G q ε S k age z D wire hist)
    (m : Memory w) (seen : ports.held r floor m) (count : ports.archive.count.base<floor)
    (wires : ports.WireRoom w floor) (homes : (old).hosts=S.hostSize age) (blocks : (old).k=k)
    (capDate : (old).cap=r.placement.cap) (groups : (old).groups=S.groupCount age)
    (native : ports.ArchiveFits k floor) (available : next<2^w) (live : 0<ports.roleLanes)
    (widths : DatePorts.ArchiveWidths G S op ports k tail p drift degree h age)
    (args : ports.argumentsPerNode=(if age=0 then 3*(S.firstWidth G.b p/p) else S.retainedArgumentsAt G drift))
    {B : BitDescription U} {number : Local B} {bounds : DatePorts.RangeRoom ports r B}
    {R : ℕ} {shape : WorldShape p R B} {label : NodeOrder.All B→Label G s Z op}
    {pointer : NodeOrder.All B→ℕ→Pointer}
    {flags : Fin (2^(old).k)→Fin ports.nodes→Fin ports.operandHosts→Fin (old).groups→ℕ}
    (actual : DatePorts.ArchiveRead ports r B number bounds shape op label pointer flags m)
    (tokenWidth : ports.tokenBits=printedBits G s Z op) (sized : ports.RoleRows) :
    ∃(data : (raw).Values) (roles : Fin (2^k)→Fin ports.operandHosts→Fin (old).groups→Cell (ports.tokenBits*ports.nodes)),
      ScheduledOldAt G S board k tail age p f gain drift degree h ordinary op s Z ports floor w supportAt r m
        homes blocks groups widths args number bounds shape label data roles:=by
  let target := L
  subst k
  obtain ⟨⟨data,stored,arity,words⟩,roles,tokens,labels⟩:=actual.pad_witness target tokenWidth sized
  refine ⟨data,roles,stored,tokens,?_,arity,words,?_⟩
  · intro x h₀ g₀
    exact labels x h₀ g₀
  · exact scheduled_venue_old G S board _ tail age p f gain drift degree h ordinary op s Z ports floor w supportAt
      r m seen count wires rfl capDate groups (native.data target) native.blocks native.roles available live
      data roles stored tokens widths homes args

/-- Derive the complete old-data input of the original reset from the actual
chronological archive. The same source words feed both the dated native movement
and its old-node arity and occupation interpretation. -/
theorem scheduled_venue_archive_old (supportAt : support) (r : Reached U G q ε S k age z D wire hist)
    (m : Memory w) (seen : ports.held r floor m) (count : ports.archive.count.base<floor)
    (wires : ports.WireRoom w floor) (homes : (old).hosts=S.hostSize age) (blocks : (old).k=k)
    (capDate : (old).cap=r.placement.cap) (groups : (old).groups=S.groupCount age)
    (native : ports.ArchiveFits k floor) (available : next<2^w) (live : 0<ports.roleLanes)
    (widths : DatePorts.ArchiveWidths G S op ports k tail p drift degree h age)
    (args : ports.argumentsPerNode=(if age=0 then 3*(S.firstWidth G.b p/p) else S.retainedArgumentsAt G drift))
    {B : BitDescription U} {number : Local B} {bounds : DatePorts.RangeRoom ports r B}
    {R : ℕ} {shape : WorldShape p R B} {label : NodeOrder.All B→Label G s Z op}
    {pointer : NodeOrder.All B→ℕ→Pointer}
    {flags : Fin (2^(old).k)→Fin ports.nodes→Fin ports.operandHosts→Fin (old).groups→ℕ}
    (actual : DatePorts.ArchiveRead ports r B number bounds shape op label pointer flags m)
    (tokenWidth : ports.tokenBits=printedBits G s Z op) (sized : ports.RoleRows) :
    ∃(data : (raw).Values) (roles : Fin (2^k)→Fin ports.operandHosts→Fin (old).groups→Cell (ports.tokenBits*ports.nodes)),
      (∀j,ports.operandHosts*chunks (old).groups ports.operandLanes≤(ports.archive.prior raw j).size ∧
        Reads (ports.archive.prior raw j) (data j) ports.operandLanes m) ∧
      (∀x,ports.operandHosts*chunks (old).groups ports.roleLanes≤(ports.archive.roles.bank x.val).size ∧
        Reads (ports.archive.roles.bank x.val) (roles x) ports.roleLanes m) ∧
      (∀x h₀ g₀,(roles x h₀ g₀).val=(encode (printedBits G s Z op) ports.nodes (fun j=>
        (DatePorts.slotAt ports r B number bounds (x.cast (congrArg (2^·) blocks.symm)) j h₀ g₀).elim 0
          (fun y=>token G s Z op (label y)))).val) ∧
      let same:=scheduled_loaded G S board k tail age p f gain drift degree h ordinary op s Z ports floor widths homes groups args
      let pages : (L).Values:=same ▸ padValues G S board k tail age p f gain drift degree h ordinary op s Z ports floor data roles
      ∀j,((entry supportAt).bank.old j).Fits w next ∧ (L).hosts*chunks (L).groups (L).previousLanes≤((entry supportAt).bank.old j).size ∧
        Reads ((entry supportAt).bank.old j) (pages j) (L).previousLanes ((publisher).image m) :=by
  obtain ⟨data,roles,stored,tokens,labels,_,_,placed⟩:=
    scheduled_venue_archive_witness G S board k tail age p f gain drift degree h ordinary op s Z ports floor w
      supportAt r m seen count wires homes blocks capDate groups native available live widths args actual tokenWidth sized
  exact ⟨data,roles,stored,tokens,labels,placed⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
