import OAI.Hierarchy.DescentCalendarPrimaryDonorWords
import OAI.Hierarchy.DescentScheduledVenueOld

namespace OAI
/-! # The registered previous donor census, pointer and range fields together -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
open DescentSixParty.Chronology DescentSIMDLookup DescentWalshPrecision DescentSixParty.PackedFlow.Padded ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open scoped Classical Fin.CommRing
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
variable (size : 2^((l).high+(l).low)=(l).groups*(l).blocks)
    (cut : (l).cut≤(l).high+(l).low) (matrix : DescentGL.Layout ((l).high+(l).low))
    (carrier : Fin (l).hosts) (hi : Block (l).cut) (d₀ : Fin (l).donors)
local notation "physical" => (l).site (fun j=>blockValues cut ((l).before size (X) j) matrix) carrier hi
local notation "src_" => (rearrange matrix).symm (DescentIssuedFallbackPanel.join cut hi d₀)
local notation "coords" => (finProdFinEquiv.symm (Fin.cast size src_) : Fin (l).groups × Fin (l).blocks)
local notation "prior" => ({(l).previousLayout with hosts:=ports.operandHosts} : DescentDatedPriorOperand.Layout)

variable (r₀ : Reached U G q ε S k age z D wire hist) (B : BitDescription U) (number : Local B)

open DescentPrimitivePalette DescentBundleHistory
variable {bound : ℕ} (room : DatePorts.RangeRoom ports r₀ B)
variable (spec : WorldShape p bound B) (label : NodeOrder.All B→Label G s Z op)
  (pointer : NodeOrder.All B→ℕ→DescentOperandStateBanks.Pointer)
  (flags : Fin (2^(old).k)→Fin ports.nodes→Fin ports.operandHosts→Fin (old).groups→ℕ)
  (mem : Memory w) (archive : DatePorts.ArchiveRead ports r₀ B number room spec op label pointer flags mem)
  (vertex_ : U.graph.Site) (node : (B.recipe vertex_).Node)
local notation "address_" => Reached.NodeCells.coordinate r₀ vertex_
local notation "block_" => (coords).2.cast (congrArg (2^·) room.radix)
local notation "host_" => (⟨(address_).1.val,room.hosts vertex_⟩ : Fin ports.operandHosts)
local notation "index_" => (number vertex_ node).castLE (room.capacity vertex_)
local notation "y_" => (⟨vertex_,node⟩ : NodeOrder.All B)
local notation "arity_" => (occurrences (spec.sites vertex_) node).length
variable (same : carrier.val=(address_).1.val ∧ (coords).1.val=(address_).2.1.val ∧ (coords).2.val=(address_).2.2.val)
variable (width : ports.operandBits*ports.nodes*ports.operandLanes≤w)
local notation "read_" f₀:arg j:arg => Reads (previousBank ports.rangeLayout ports.archive.arguments block_
    (DescentOperandStateBanks.page f₀ j)) (data ((l).sourceID ((l).operandField f₀ j) (coords).2)) ports.operandLanes mem

section SourceFamily
variable {I : Type} (site : I→U.graph.Site) (donors : I→Fin (l).donors)
local notation "row_" u => (finProdFinEquiv.symm (Fin.cast size
  ((rearrange matrix).symm (DescentIssuedFallbackPanel.join cut hi (donors u)))) : Fin (l).groups×Fin (l).blocks)
local notation "book_" u => spec.sites (site u)
local notation "addr_" u => Reached.NodeCells.coordinate r₀ (site u)
local notation "node_" u:arg n:arg => (number (site u) n).castLE (room.capacity (site u))
variable (sameRows : ∀u,carrier.val=(addr_ u).1.val ∧ (row_ u).1.val=(addr_ u).2.1.val ∧
  (row_ u).2.val=(addr_ u).2.2.val)
variable (hp : 0<p) (priorArgs : ∀u n,((book_ u).recipe hp).arity n≤ports.argumentsPerNode)
variable (fits : ports.argumentsPerNode<2^ports.operandBits)
local notation "published_" x => DatePorts.metadataPage ports 1 ((x).cast (congrArg (2^·) room.radix))
local notation "word_" u:arg n:arg field₀:arg => (l).entry physical (donors u) (node_ u n) field₀
variable (supportAt:support) (homes : (old).hosts=S.hostSize age) (blocks : (old).k=k)
    (groups : (old).groups=S.groupCount age) (widths : DatePorts.ArchiveWidths G S op ports k tail p drift degree h age)
    (args : ports.argumentsPerNode=(if age=0 then 3*(S.firstWidth G.b p/p) else S.retainedArgumentsAt G drift))
    (sized : ports.RoleRows) (alphabet : ports.tokenBits=printedBits G s Z op)
    (rolePos : 0<ports.roleLanes) (roleRoom : ports.tokenBits*ports.nodes*ports.roleLanes≤w)
    (pop : Fintype.card r₀.V≤ports.operandHosts) (top : Fintype.card r₀.V≤(old).hosts)
    (positive : 0<ports.operandBits)
local notation "scheduled_" => ScheduledOldAt G S board k tail age p f gain drift degree h ordinary op s Z ports floor w
  supportAt r₀ mem homes blocks groups widths args number room spec label data roles
local notation "root_" d => (rearrange matrix).symm (DescentIssuedFallbackPanel.join cut hi (d:Fin (l).donors))
local notation "rect_" d => (finProdFinEquiv.symm (Fin.cast size (root_ d)) : Fin (l).groups × Fin (l).blocks)
local notation "homeName" => r₀.vertex.trans (Fin.castLEEmb top)

include archive sameRows width fits sized alphabet rolePos roleRoom pop positive in
/-- This single previous panel is precisely the one read by the installed chronological
reset. Its full original population is recovered from real tokens, including unpaid
nullaries; its complete original operands come from the same padded input. -/
theorem named_primary_donor_words (stored : scheduled_) :
    (∀d : Fin (l).donors,(l).originalCount physical d=∑v,if DescentPaidResidentCount.occupies r₀.placement
      (Equiv.refl _) homeName carrier ((rect_ d).1.cast room.groups.symm) (rect_ d).2 v
      then Fintype.card (B.recipe v).Node else 0) ∧
    (∀u n,(word_ u n ((l).arityField)).val=((book_ u).recipe hp).arity n) ∧
    (∀u n (j : Fin (((book_ u).recipe hp).arity n)) (f₀ : Fin 4),
      (word_ u n ((l).operandField (f₀.castLE (by decide : 4≤7)) (j.castLE (priorArgs u n)))).val=
        (pointer ⟨site u,n⟩ j.val).header f₀) ∧
    (∀u n (j : Fin (((book_ u).recipe hp).arity n)) (f₀ : Fin 3),
      (word_ u n ((l).operandField (DescentRetainedRangeDigits.page f₀) (j.castLE (priorArgs u n)))).val=
        atSlot (book_ u) n j.val f₀):=by
  obtain ⟨_,loadedRoles,_,loadedArity,loadedFields,_⟩:=stored
  constructor
  · intro d
    exact registered_original_count (G:=G) (S:=S) (board:=board) (k:=k) (tail:=tail) (age:=age) (p:=p)
      (f:=f) (gain:=gain) (drift:=drift) (degree:=degree) (h:=h) (ordinary:=ordinary) (op:=op)
      (s:=s) (Z:=Z) (ports:=ports) (floor:=floor) (w:=w) (r₀:=r₀) (B:=B) (number:=number) (data:=data) (roles:=roles) (size:=size) (cut:=cut)
      (matrix:=matrix) (carrier:=carrier) (hi:=hi) (d₀:=d) (population:=pop) (topHosts:=top)
      room spec label pointer flags mem archive sized alphabet rolePos roleRoom (fun x=>(loadedRoles x).2) positive
  · apply calendar_fibre_headers (data:=data) (roles:=roles) (matrix:=matrix) (site:=site) (donors:=donors)
      (archive:=archive) (sameRows:=sameRows) (width:=width) (hp:=hp) (priorArgs:=priorArgs) (fits:=fits)
    · intro x
      change Reads _ (data ((raw).sourceID (raw).arityField x)) _ _
      rw [loadedArity]
      exact archive.arity _
    · exact loadedFields

end SourceFamily
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
