import OAI.Hierarchy.DescentSignedLayout
import OAI.Hierarchy.DescentSignedPrefixReceipt
import OAI.Hierarchy.DescentOrdinaryCompactPeerROM
import OAI.Hierarchy.DescentOrdinarySocketPeer
import OAI.Hierarchy.DescentOrdinaryRankIssued
import OAI.Hierarchy.DescentOrdinarySourceReceipt
import OAI.Hierarchy.DescentOrdinaryRawControlsRAM
import OAI.Hierarchy.DescentOrdinarySignedNative
import OAI.Hierarchy.DescentOrdinarySignedInvoice
import OAI.Hierarchy.DescentSignedPrimitiveBanks

namespace OAI
/-! Fixed append-only signed device. All address expressions are evaluated on
RAM. The public plan contains no graph, edge, chosen matching or stored data. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSixParty.Chronology DescentHaloWalkRAM DescentSIMDLookup DescentDyadicSpan DescentPackedColony
open DescentParallelBase DescentParallelBase.ParentFilter DescentPackedZip DescentOrdinarySignedDate DescentOrdinarySignedMeta
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (s:SignedExtent) {w : ℕ}
abbrev Socket:=Fin s.blocks×Fin s.candidates
abbrev Consumer:=(Fin s.blocks×Fin 3)×(Fin s.candidates×Fin (s.candidates+1))
def sockets:=s.blocks*s.candidates
def requests:=(s.blocks*3)*(s.candidates*(s.candidates+1))
def socketId : Socket s≃Fin s.sockets:=finProdFinEquiv
def requestId : Consumer s≃Fin s.requests:=(finProdFinEquiv.prodCongr finProdFinEquiv).trans finProdFinEquiv
/-- Numerical earlier addresses. Rooted forward and backward path digits come
from the actual path/rebase tables. No function in this ABI maps a
next-edge label to its signed successor sheet. -/
structure Input (s:SignedExtent) where
  newDegree : ℕ
  hostPitch : ℕ
  rankBanks:DescentOrdinaryDonorRankDirectory.Banks
  path:Socket s→Expr
  endpoints:Socket s→Bool→Expr
  donor:Socket s→Fin 6→Expr
  mark:Socket s→Expr
  priorRanks : Bank
  priorEnds : Bank
  newNeighbors : Bank
  donorForward : Fin s.blocks→Fin s.residentSlots→Expr
  donorLow : Fin s.blocks→Fin s.residentSlots→Expr
  reversePath:Bank
  ports:Ports s.reach

/-- A lane survives only when the actual 11-field donor passes the incidence
test. Comparing the complete word with zero would mix unrelated groups. -/
def keepField {b:ℕ} (flag:Cell (1*4)) (value:Cell b):Cell b:=if flag.val=0 then 0 else value
def gatePages (b M:ℕ):=DescentOrdinaryAtomFieldRAM.ROM.binary (keepField (b:=b)) M
def gateWidth (b M:ℕ):=(4+b)*M
def gateTable (base b M:ℕ):=DescentOrdinaryAtomFieldRAM.ROM.joined (gatePages b M) (gateWidth b M) base id
def fieldIndex:Fin 3→DescentOrdinaryDonorRankDirectory.Field:=![.reverse,.localEndpoint,.sharedEndpoint]
def fieldNumber:DescentOrdinaryDonorRankDirectory.Field→ℕ
  | .reverse=>0 | .localEndpoint=>1 | .sharedEndpoint=>2
def pairIndex {m n:ℕ} (a:Fin m) (b:Fin n):ℕ:=(finProdFinEquiv (a,b)).val
def localId (z:Socket s) (f:Fin 11):ℕ:=pairIndex (socketId s z) f
def projectedId (z:Socket s) (f:Fin 11) (l:Fin s.lowSites):ℕ:=pairIndex (finProdFinEquiv (socketId s z,f)) l
def returnedId (c:Consumer s) (f:Fin 11):ℕ:=pairIndex (requestId s c) f

def hdrRows:=s.priorHosts*(s.reach*s.reach)
def viewRows:=s.hosts*(s.reach*s.reach)
def oldSlab:=s.priorHosts*chunks s.groups s.lanes
def routeBits:=(DescentSharedCableNames.Packed.bits s.routeTotal+s.fieldBits)*s.lanes
def mapBase (base:ℕ):=base+s.directoryWords
def mapTranspose (base:ℕ):=mapBase s base+span s.viewRows
def mapHost (base:ℕ):=mapTranspose s base+s.lowSites*span s.oldSlab
def mapChunk (base:ℕ):=mapHost s base+span s.slab
def mapOffset (base:ℕ):=mapChunk s base+span s.slab
def mapIndices:=span s.viewRows+s.lowSites*span s.oldSlab+span s.slab+span s.slab+span s.priorHosts
def reverseBits:=DescentSharedCableNames.Packed.bits s.reach
def reverseLookup:=DescentPackedChildNeighbor.SIMD.ROM.cells s.reach s.reverseBits s.reverseBits s.lanes s.priorHosts s.groups+(span s.oldSlab-s.oldSlab)
def mapWords:=s.mapIndices+s.reverseLookup
def reverseBase (base:ℕ):=mapBase s base+s.mapIndices
def viewBase (base:ℕ):=mapBase s base+s.mapWords
def keyStart (base:ℕ):=viewBase s base+3*span s.viewRows
def lookupStart (base:ℕ):=DescentOrdinaryDonorSources.PathKeys.endAddress (keyStart s base) s.fieldBits s.lanes
def lookupWords:=DescentPackedChildNeighbor.SIMD.ROM.cells (s.reach*s.reach) s.fieldBits s.fieldBits s.lanes s.hosts s.groups + (span s.slab-s.slab)
def ranksStart (base:ℕ):=lookupStart s base+s.lookupWords
def peerStart (base:ℕ):=ranksStart s base+(s.sockets*5)*span s.slab
def localStart (base:ℕ):=DescentOrdinaryDonorSources.ROM.endAddress (peerStart s base) s.fieldBits s.lanes
def projectedStart (base:ℕ):=localStart s base+(s.sockets*11)*span s.slab
def forwardBase (base:ℕ):=projectedStart s base+((s.sockets*11)*s.lowSites)*span s.oldSlab
def forwardBits:=(DescentSharedCableNames.Packed.bits s.reach+DescentSharedCableNames.Packed.bits s.lowSites)*s.lanes
def finishBits:=(DescentSharedCableNames.Packed.bits (s.reach*s.lowSites)+DescentSharedCableNames.Packed.bits s.reach)*s.lanes
def backBase (base:ℕ):=forwardBase s base+2*2^s.forwardBits
def routeStart (base:ℕ):=backBase s base+2*2^s.finishBits
def returnedStart (base:ℕ):=routeStart s base+(s.routeTotal*2)*2^s.routeBits
def shapesStart (base:ℕ):=returnedStart s base+(s.requests*11)*span s.oldSlab
def rawStart (base:ℕ):=shapesStart s base+Fused.TablesROM.length s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes
def metaStart (base:ℕ):=RawControls.stop (rawStart s base) s.fieldBits s.lanes
def gateStart (base:ℕ):=DescentOrdinarySignedMeta.stop (metaStart s base) s.fieldBits s.lanes
def peerKeyBase (base:ℕ):=gateStart s base+2*2^gateWidth s.fieldBits s.lanes
def peerROMBase (base:ℕ):=peerKeyBase s base+2^DescentOrdinarySocketPeer.bits s.fieldBits s.lanes
def peerBits:=DescentSharedCableNames.Packed.bits s.peerKinds
def peerLookupWords:=DescentPackedChildNeighbor.SIMD.ROM.cells s.peerKinds s.peerBits s.fieldBits s.lanes s.hosts s.groups+(span s.slab-s.slab)
def peerHeadBase (base:ℕ):=s.peerROMBase base+s.peerLookupWords
def peerHeadRows:=s.hosts*s.peerKinds
def peerHeadWords:=DescentOrdinaryCompactPeer.ROM.count s.priorHosts s.hosts (s.reach*s.reach) s.lowSites+span (s.peerHeadRows+1)+span (s.priorHosts+1)
def peerHeadOut (base:ℕ):=s.peerHeadBase base+s.peerHeadWords
def peerDirectory (base:ℕ):=subbank (s.peerHeadOut base) s.peerHeadRows 0
def peerHeadExpr (input:s.Input) (base:ℕ):Expr:=
  let lo:=s.peerHeadBase base
  let L:=s.reach*s.reach
  DescentOrdinaryCompactPeer.expr (DescentOrdinaryCompactPeer.ROM.layout lo s.priorHosts s.hosts L s.lowSites input.priorRanks input.priorEnds input.newNeighbors)
    (DescentOrdinaryCompactPeer.ROM.shapes lo s.hosts L s.lowSites 0) s.priorHosts L input.newDegree
def tailStart (base:ℕ):=s.peerHeadOut base+span s.peerHeadRows

def rawField (base:ℕ) (z:Socket s) (f:Fin 11):Expr:=.lookup (subbank (localStart s base) s.slab (localId s z f)) .row

def gathered (base:ℕ) (z:Socket s):Expr:=
  DescentPacking.PackedMatch.Local.Gather.assembly
    (Fused.TablesROM.joins s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes (shapesStart s base))
    (rawField s base z)
def peerField (_input:s.Input) (base:ℕ) (z:Socket s):Expr:=
  let key:=DescentOrdinarySocketPeer.query (s.peerKeyBase base) s.fieldBits s.lanes (s.gathered base z)
  let chart:=DescentPackedChildNeighbor.SIMD.ROM.layout (s.peerROMBase base) s.peerKinds s.peerBits s.fieldBits s.lanes (Nat.clog 2 s.slab) (s.peerDirectory base)
  DescentPackedChildNeighbor.SIMD.body chart key (List.finRange s.peerKinds)
def flags (input:s.Input) (base:ℕ) (z:Socket s):Expr:=
  (RawControls.flagsTable (rawStart s base) s.fieldBits s.fieldBits s.lanes).read (s.gathered base z) (input.mark z)
def publicIndex (pitch i:ℕ):ℕ:=
  let P:=s.reach;let N:=chunks s.groups s.lanes
  if i<span s.viewRows then
    let old:=(i/(P*P))/pitch
    if 0<pitch ∧ old < s.priorHosts then old*(P*P)+i%(P*P) else s.hdrRows
  else
    let j:=i-span s.viewRows
    if j < s.lowSites*span s.oldSlab then
      let row:=j%span s.oldSlab;let low:=j/span s.oldSlab;let host:=row/N*pitch+low
      if low<pitch ∧ host < s.hosts then host*N+row%N else s.slab
    else
      let t:=j-s.lowSites*span s.oldSlab
      if t<span s.slab then (if pitch=0 then s.priorHosts else min ((t/N)/pitch) s.priorHosts)*P
      else if t-span s.slab<span s.slab then (t-span s.slab)%N
      else (t-span s.slab-span s.slab)*N
def maps (pitch i:ℕ):ℕ:=
  if i < s.mapIndices then s.publicIndex pitch i else
    DescentPackedChildNeighbor.SIMD.ROM.numbers s.reach s.reverseBits s.reverseBits s.lanes s.priorHosts s.groups (i-s.mapIndices)
def indexed (pointer:Expr) (sentinel:ℕ) (B:Bank):Expr:=
  .branch .eq pointer (.lit sentinel) (.lit 0) (.lookup B pointer)
def socketAt (c:Consumer s):Socket s:=(c.1.1,Fin.cases c.2.1 id c.2.2)
def priorSlot (c:Consumer s):Fin s.reach×Fin s.residentSlots:=finProdFinEquiv.symm c.2.1
def sourceAt (c:Consumer s) (back:Fin s.reach):Socket s:=(c.1.1,Fin.cases (finProdFinEquiv (back,(priorSlot s c).2)) id c.2.2)
def remoteWord (input:s.Input) (base:ℕ) (c:Consumer s) (f:Fin 11):Expr:=
  let h:Expr:=.lookup (subbank (mapHost s base) s.slab 0) .row
  let root:Expr:=.lookup input.rankBanks.endpoints (.op .add h (.lit (priorSlot s c).1.val))
  let off:Expr:=.lookup (subbank (mapOffset s base) s.priorHosts 0) root
  let chunk:Expr:=.lookup (subbank (mapChunk s base) s.slab 0) .row
  let word:Expr:=.lookup (subbank (returnedStart s base) s.oldSlab (returnedId s c f)) (.op .add off chunk)
  .branch .eq h (.lit (s.priorHosts*s.reach)) (.lit 0) (.branch .eq root (.lit s.priorHosts) (.lit 0) word)
def operand (input:s.Input) (base:ℕ) (c:Consumer s) (f:Fin 11):Expr:=
  let value:=if c.1.2.val=2 then s.remoteWord input base c f else rawField s base (socketAt s c) f
  (gateTable (gateStart s base) s.fieldBits s.lanes).read (s.flags input base (c.1.1,c.2.1)) value
def layout (input:s.Input) (base:ℕ):Layout s.blocks s.candidates where
  header x j:=let z:Socket s:=(x,j)
              let units:=(RawControls.unitsTable (rawStart s base) s.fieldBits s.fieldBits s.lanes).read (s.gathered base z) (input.mark z)
              DescentOrdinarySignedMeta.mountedExpr (metaStart s base) input.newDegree s.fieldBits s.lanes (s.flags input base z) (s.peerField input base z) units
  query x p j:=s.operand input base ((x,p),(j,0))
  items x p j i:=s.operand input base ((x,p),(j,i.succ))

def rankField (input:s.Input) (base:ℕ) (z:Socket s) (i:Fin 5):Expr:=
  let P:=s.reach;let b:=s.fieldBits;let M:=s.lanes
  let mtab:=DescentOrdinaryDonorSources.PathKeys.table (keyStart s base) s.degree b b M
  let key:=mtab.read (input.path z) (input.endpoints z (DescentOrdinaryDonorSources.PathKeys.side i))
  let dir:=subbank (viewBase s base) s.viewRows (fieldNumber (DescentOrdinaryDonorSources.tag i))
  let tbl:=DescentPackedChildNeighbor.SIMD.ROM.layout (lookupStart s base) (P*P) b b M (Nat.clog 2 s.slab) dir
  DescentPackedChildNeighbor.SIMD.body tbl key (List.finRange (P*P))
def rankPage (base:ℕ) (z:Socket s) (i:Fin 5):Bank:=
  subbank (ranksStart s base) s.slab (pairIndex (s.socketId z) i)
def donorField (input:s.Input) (base:ℕ) (z:Socket s) (f:Fin 11):Expr:=
  let ptab:=DescentOrdinaryDonorSources.ROM.table (peerStart s base) s.lowSites s.fieldBits s.lanes
  DescentOrdinaryDonorSources.assemble ptab (input.donor z) (fun i=>.lookup (s.rankPage base z i) .row) f
def transposed (base:ℕ) (i:Fin (s.sockets*11)) (l:Fin s.lowSites):Expr:=
  indexed (.lookup (subbank (mapTranspose s base) s.oldSlab l.val) .row) s.slab (subbank (localStart s base) s.slab i.val)
def backDigit (input:s.Input) (base:ℕ) (x:Fin s.blocks) (o:Fin s.residentSlots):Expr:=
  let chart:=DescentPackedChildNeighbor.SIMD.ROM.layout (s.reverseBase base) s.reach s.reverseBits s.reverseBits s.lanes (Nat.clog 2 s.oldSlab) input.reversePath
  DescentPackedChildNeighbor.SIMD.body chart (input.donorForward x o) (List.finRange s.reach)
def routeQuery (input:s.Input) (base:ℕ) (x:Fin s.blocks) (o:Fin s.residentSlots):Expr:=
  let P:=s.reach;let M:=s.lanes
  let forward:=DescentOrdinaryAtomFieldRAM.ROM.binary (SourceReturn.Query.forward P s.lowSites) M
  let back:=DescentOrdinaryAtomFieldRAM.ROM.binary (SourceReturn.Query.finish P s.lowSites) M
  let ts:=DescentOrdinaryAtomFieldRAM.ROM.joined forward s.forwardBits (forwardBase s base) id
  let tr:=DescentOrdinaryAtomFieldRAM.ROM.joined back s.finishBits (backBase s base) id
  SourceReturn.Query.expr ts tr (input.donorForward x o) (input.donorLow x o) (s.backDigit input base x o)
def routed (input:s.Input) (base:ℕ) (c:Consumer s) (f:Fin 11):Expr:=
  let P:=s.reach
  if c.1.2.val=2 then SourceReturn.RAM.body (SourceReturn.RAM.ROM.table P s.lowSites s.fieldBits s.lanes (routeStart s base))
    input.ports (fun l rev=>subbank (projectedStart s base) s.oldSlab (projectedId s (sourceAt s c rev) f l))
    (s.routeQuery input base c.1.1 (priorSlot s c).2) s.priorHosts else .lit 0

def jobs (input:s.Input) (base:ℕ):List job:=
  let P:=s.reach;let b:=s.fieldBits;let M:=s.lanes
  let rankJob (r:Fin (s.sockets*5)):=let t:Fin s.sockets×Fin 5:=finProdFinEquiv.symm r
    s.rankField input base (s.socketId.symm t.1) t.2
  let localJob (r:Fin (s.sockets*11)):=let t:Fin s.sockets×Fin 11:=finProdFinEquiv.symm r
    s.donorField input base (s.socketId.symm t.1) t.2
  let projectJob (r:Fin ((s.sockets*11)*s.lowSites)):=let t:Fin (s.sockets*11)×Fin s.lowSites:=finProdFinEquiv.symm r
    s.transposed base t.1 t.2
  let routeJob (r:Fin (s.requests*11)):=let t:Fin s.requests×Fin 11:=finProdFinEquiv.symm r
    s.routed input base (s.requestId.symm t.1) t.2
  [col 3 s.hdrRows (fromIndex (fun f:Fin 3=>DescentOrdinaryDonorRankDirectory.expression input.rankBanks s.priorHosts (fieldIndex f))),
   .words s.mapWords (s.maps input.hostPitch),
   col 3 s.viewRows (fromIndex (fun f:Fin 3=>indexed (.lookup (subbank (mapBase s base) s.viewRows 0) .row) s.hdrRows (subbank base s.hdrRows f.val))),
   lit (DescentOrdinaryDonorSources.PathKeys.pages s.degree b b M) (DescentOrdinaryDonorSources.PathKeys.width b M),
   .words s.lookupWords
     (DescentPackedChildNeighbor.SIMD.ROM.numbers (P*P) b b M s.hosts s.groups),
   col (s.sockets*5) s.slab (fromIndex rankJob),
   lit (DescentOrdinaryDonorSources.ROM.pages s.lowSites b M) (DescentOrdinaryDonorSources.ROM.width b M),
   col (s.sockets*11) s.slab (fromIndex localJob),
   col ((s.sockets*11)*s.lowSites) s.oldSlab (fromIndex projectJob),
   lit (DescentOrdinaryAtomFieldRAM.ROM.binary (SourceReturn.Query.forward P s.lowSites) M) s.forwardBits,
   lit (DescentOrdinaryAtomFieldRAM.ROM.binary (SourceReturn.Query.finish P s.lowSites) M) s.finishBits,
   lit (SourceReturn.RAM.ROM.book P s.lowSites b M) s.routeBits,
   col (s.requests*11) s.oldSlab (fromIndex routeJob),
   lit (Fused.TablesROM.pages s.degree s.lowSites s.tickets s.cap b M) (Fused.TablesROM.unit s.degree s.lowSites s.tickets s.cap b*M),
   lit (RawControls.pages b b M) (RawControls.width b M),
   lit (DescentOrdinarySignedMeta.pages input.newDegree b M) (DescentOrdinarySignedMeta.pageBits b M),
   lit (gatePages b M) (gateWidth b M),
   .words (2^DescentOrdinarySocketPeer.bits b M) (DescentOrdinarySocketPeer.table s.degree s.lowSites s.tickets s.cap b M),
   .words s.peerLookupWords (DescentPackedChildNeighbor.SIMD.ROM.numbers s.peerKinds s.peerBits b M s.hosts s.groups),
   .words s.peerHeadWords (DescentOrdinaryCompactPeer.ROM.contents s.priorHosts s.hosts (P*P) s.lowSites input.newDegree input.hostPitch),
   col 1 s.peerHeadRows (fun _=>s.peerHeadExpr input base)]

theorem finish_jobs (input:s.Input) (base:ℕ):SignedPrefix.finish (s.jobs input base) base=s.tailStart base:=by
  simp only [jobs,SignedPrefix.finish,SignedPrefix.Job.width,col,lit,tailStart,peerHeadOut,peerHeadBase,peerROMBase,peerKeyBase,gateStart,metaStart,rawStart,shapesStart,
    returnedStart,routeStart,backBase,forwardBase,projectedStart,localStart,peerStart,ranksStart,lookupStart,lookupWords,keyStart,viewBase,
    mapBase,mapWords,mapIndices,reverseLookup,reverseBits,DescentOrdinarySignedMeta.stop,RawControls.stop,
    Fused.TablesROM.length,DescentOrdinaryDonorSources.ROM.endAddress,DescentOrdinaryDonorSources.PathKeys.endAddress,
    directoryWords,hdrRows,routeTotal,Nat.add_assoc]
 ; ring

def kernel (input:s.Input) (base w : ℕ):NativePhase w:=
  let lay:=s.layout input base
  let end':=s.tailStart base
  ⟨Layout.program lay end' s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes input.newDegree s.hosts s.groups w,
   Layout.time lay end' s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes input.newDegree s.hosts s.groups,
   Layout.memory lay end' s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes input.newDegree s.hosts s.groups,by
     apply cheap_seq
     · apply cheap_seq <;> apply DescentOrdinaryAtomFieldRAM.ROM.cheap
     · apply cheap_seq
       · apply cheap_seq
         · apply DescentOrdinaryAtomFieldRAM.ROM.cheap
         · apply program_cheap
       · apply cheap_seq
         · apply DescentOrdinaryAtomFieldRAM.ROM.cheap
         · apply cheap_seq
           · apply DescentOrdinaryAtomFieldRAM.ROM.cheap
           · apply program_cheap⟩

def phase (input:s.Input) (base w:ℕ):NativePhase w:=
  SignedPrefix.build w (fun _=>s.kernel input base w) (s.jobs input base) base
def phaseTicks (input:s.Input) (base w:ℕ):ℕ:=(s.phase input base w).ticks
def phaseImage (input:s.Input) (base:ℕ) (m:Memory w):Memory w:=(s.phase input base w).image m
def phaseEnd (base:ℕ):=
  let p:=DescentOrdinarySignedParents.ROM.endAddress (s.tailStart base) s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes
  DescentOrdinarySignedAll.endAddress p s.blocks s.candidates s.cap s.fieldBits s.lanes s.hosts s.groups

open DescentNextSignedWindow DescentResetSignedScan in
theorem core_calibrated (s:SignedExtent) (base:ℕ):
    DescentOrdinarySignedAll.endAddress (DescentOrdinarySignedParents.ROM.endAddress (DescentOrdinaryDonorSources.ROM.endAddress (base+s.directoryWords) s.fieldBits s.lanes)
      s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes) s.blocks s.candidates s.cap s.fieldBits s.lanes s.hosts s.groups=s.coreRoof base:=by
  simp only [DescentOrdinaryDonorSources.ROM.endAddress,DescentOrdinaryDonorSources.ROM.width,DescentOrdinarySignedParents.ROM.endAddress,DescentOrdinarySignedAll.endAddress,
    DescentOrdinarySignedAll.Tail,DescentResetWindowTail.endAddress,DescentResetWindowTail.next,
    DescentResetFieldAssembler.endAddress,DescentResetFieldAssembler.width,Native.All.endAddress,Native.All.headWords,Native.All.pageCount,
    Native.ROM.width,Native.All.count,Ranks.endAddress,Ranks.start,Ranks.headWords,Ranks.count,Ranks.width,Fused.TablesROM.length,
    DescentOrdinarySignedParents.ROM.width,coreRoof,signedBound,peerWords,converterWords,compareWidth,rankWords,formatterWords,outputWords,slab,digitArea,candidates,reach]
  ring_nf

theorem calibrated (base:ℕ):s.phaseEnd base=s.roof base:=by
  unfold phaseEnd
  simp only [DescentOrdinaryDonorSources.ROM.endAddress,DescentOrdinaryDonorSources.ROM.width,DescentOrdinarySignedParents.ROM.endAddress,DescentOrdinarySignedAll.endAddress,
    DescentOrdinarySignedAll.Tail,DescentResetWindowTail.endAddress,DescentResetWindowTail.next,
    DescentResetFieldAssembler.endAddress,DescentResetFieldAssembler.width,DescentNextSignedWindow.Native.All.endAddress,
    DescentNextSignedWindow.Native.All.headWords,DescentNextSignedWindow.Native.All.pageCount,DescentNextSignedWindow.Native.ROM.width,
    DescentNextSignedWindow.Native.All.count,DescentResetSignedScan.Ranks.endAddress,DescentResetSignedScan.Ranks.start,
    DescentResetSignedScan.Ranks.headWords,DescentResetSignedScan.Ranks.count,DescentResetSignedScan.Ranks.width,
    DescentOrdinarySignedParents.ROM.width,roof,coreRoof,signedBound,peerWords,converterWords,compareWidth,rankWords,formatterWords,outputWords,
    preparation,indexWords,oldKey,oldRows,remoteArea,flagArea,shapeArea,gateArea,forwardArea,backArea,reverseWords,peerSelectionWords,shortPeerKinds,DescentOrdinarySocketPeer.bits,digitArea,jobsLocal,jobsCompare,slab,
    tailStart,peerHeadOut,peerHeadWords,peerHeadBase,peerHeadRows,DescentOrdinaryCompactPeer.ROM.count,peerDirectoryWords,peerLookupWords,peerROMBase,peerKeyBase,peerBits,peerKinds,gateStart,metaStart,rawStart,shapesStart,returnedStart,routeStart,backBase,forwardBase,projectedStart,localStart,peerStart,ranksStart,
    lookupStart,lookupWords,keyStart,viewBase,mapBase,mapWords,mapIndices,reverseLookup,reverseBits,DescentOrdinarySignedMeta.stop,RawControls.stop,
    RawControls.width,DescentOrdinarySignedMeta.pageBits,gateWidth,Fused.TablesROM.length,DescentOrdinaryDonorSources.PathKeys.endAddress,
    DescentOrdinaryDonorSources.PathKeys.width,directoryWords,viewRows,routeTotal,routeBits,forwardBits,finishBits,oldSlab,sockets,requests]
  ring_nf

structure Fits (s:SignedExtent) (input:s.Input) (base w:ℕ):Prop where
  «prefix»:SignedPrefix.Fits w (s.jobs input base) base
  header:∀x j,((s.layout input base).header x j).Fits w (s.tailStart base)
  query:∀x p j f,((s.layout input base).query x p j f).Fits w (s.tailStart base)
  items:∀x p j t f,((s.layout input base).items x p j t f).Fits w (s.tailStart base)

theorem phase_any (input:s.Input) (base w:ℕ) (m:Memory w) (fits:s.Fits input base w) (space:s.phaseEnd base<2^w):
    (s.phase input base w).program.Exec m (s.phaseImage input base m) (s.phaseTicks input base w) ∧
    (∀a,a<base ∨ s.phaseEnd base≤a→s.phaseImage input base m a=m a) ∧ CheapCode (s.phase input base w).program:=by
  have ord:s.tailStart base ≤ s.phaseEnd base:=by
    let a:=DescentOrdinarySignedParents.ROM.endAddress (s.tailStart base) s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes
    have a₀:s.tailStart base≤a:=by dsimp [a,DescentOrdinarySignedParents.ROM.endAddress];omega
    have hi:=DescentOrdinarySignedAll.ordered (X:=s.blocks) (K:=s.candidates) (b:=s.fieldBits) (M:=s.lanes) (H:=s.hosts) (gg:=s.groups) (cap:=s.cap) a
    exact a₀.trans (hi.1.trans hi.2)
  have tail (m':Memory w):=(Layout.any (s.layout input base) (s.tailStart base) s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes
    input.newDegree s.hosts s.groups w m' fits.header fits.query fits.items space)
  have checked:=SignedPrefix.run (fun _=>s.kernel input base w) (s.jobs input base) base (s.phaseEnd base) m fits.prefix space
    (by rw [s.finish_jobs input base];exact ord) (fun m'=>⟨(tail m').1,by
      rw [s.finish_jobs input base]
      exact (tail m').2.1⟩)
  exact ⟨checked.1,checked.2,(s.phase input base w).cheap⟩

/-- Common-stage image preceding the three weighted ranks and final output. -/
def installed (input:s.Input) (base:ℕ) (m:Memory w):Memory w:=SignedPrefix.earlier (s.jobs input base) base m
def page (base:ℕ) (x:Fin s.blocks) (j:Fin (2*s.cap)):Bank:=
  DescentOrdinarySignedAll.page (DescentOrdinarySignedParents.ROM.endAddress (s.tailStart base) s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes)
    s.blocks s.candidates s.cap s.fieldBits s.lanes s.hosts s.groups x j
theorem prefix_room (base:ℕ):s.tailStart base ≤ s.phaseEnd base:=by
  let a:=DescentOrdinarySignedParents.ROM.endAddress (s.tailStart base) s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes
  have a₀:s.tailStart base≤a:=by dsimp [a,DescentOrdinarySignedParents.ROM.endAddress];omega
  have h:=DescentOrdinarySignedAll.ordered (X:=s.blocks) (K:=s.candidates) (b:=s.fieldBits) (M:=s.lanes) (H:=s.hosts) (gg:=s.groups) (cap:=s.cap) a
  exact a₀.trans (h.1.trans h.2)
theorem installed_words (input:s.Input) (base:ℕ) (m:Memory w) (fits:s.Fits input base w) (space:s.roof base<2^w):
    SignedPrefix.Written (s.installed input base m) (s.jobs input base) base ∧
    ∀a<base,s.installed input base m a=m a:=by
  have enough:SignedPrefix.finish (s.jobs input base) base<2^w:=by
    rw [s.finish_jobs input base]
    exact (s.prefix_room base).trans_lt ((s.calibrated base).symm ▸ space)
  exact ⟨SignedPrefix.written _ _ _ fits.prefix enough,SignedPrefix.earlier_below _ _ _ fits.prefix enough⟩
theorem phase_output (input:s.Input) (base:ℕ) (m:Memory w):
    s.phaseImage input base m=Layout.memory (s.layout input base) (s.tailStart base) s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes input.newDegree s.hosts s.groups
      (s.installed input base m):=SignedPrefix.output _ _ _ _

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
