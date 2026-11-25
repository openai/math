import OAI.Hierarchy.DescentResetSourceTicketPair
import OAI.Hierarchy.DescentResetSourceSeekRAM
import OAI.Hierarchy.DescentResetLocalRankRAM

namespace OAI
/-! # Numeric reset dates for source-ticket publication, transport, and both receiver positions -/
namespace Hierarchy.DescentResetRankedWindows
open DescentPackedColony DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical
noncomputable section

/-- All numeric admission and word tables of this date are chosen before it executes.
The two input expressions address previous raw metadata and original cable words. -/
structure Layout (X K : ℕ) where
  base : ℕ
  bits : ℕ
  originalBits : ℕ
  lanes : ℕ
  hosts : ℕ
  groups : ℕ
  ports : Ports 4
  before : ℕ→ℕ→Bool
  sourceSlot : Fin K→ℕ→ℕ
  header : Fin X→Fin K→Expr
  original : Fin X→Fin K→Expr

namespace Layout
variable {X K w : ℕ} (L : Layout X K)

def ticketBase:=DescentResetSourceTicketPair.endAt L.base L.bits L.originalBits L.lanes
def seekBase:=DescentResetSourceTicketBank.endAddress L.ticketBase L.originalBits L.lanes L.hosts L.groups X K
def rankBase:=DescentResetSourceSeekRAM.endAddress L.seekBase 4 K L.bits L.originalBits L.bits L.lanes
def endAddress:=DescentResetLocalRankRun.endAddress L.rankBase X K L.bits L.lanes L.hosts L.groups
def oldBank (x : Fin X) (j : Fin K) :=DescentResetSourceTicketBank.column L.ticketBase L.originalBits L.lanes L.hosts L.groups K x.val j.val
def localBank (x : Fin X) (a : Fin 3) (j : Fin K) :=DescentResetLocalRankRun.bank L.rankBase X K L.bits L.lanes L.hosts L.groups x a j
def search (j : Fin K):=DescentResetSourceSeekRAM.tables L.seekBase 4 K L.bits L.originalBits L.lanes L.sourceSlot j
def lookup:=DescentResetSourcePullRAM.menus (DescentResetSourceSeekRAM.keyBits 4 K) L.bits L.lanes 4 K
  (DescentResetSourceSeekRAM.addressEnd L.seekBase K L.bits L.originalBits L.lanes)
def pull (x : Fin X) (j : Fin K) (old : Fin K→Bank) :=
  DescentResetSourcePullRAM.instruction L.lookup ((L.search j).read (L.header x j) (L.original x j)) L.ports old L.hosts
def ticket (x : Fin X) (j : Fin K) :=L.pull x j (L.oldBank x)
def finalRank (x : Fin X) (p : Fin 3) (j : Fin K) : Expr :=
  if p=2 then L.pull x j (L.localBank x 0) else .lookup (L.localBank x p j) .row
def questions:=DescentResetSourceTicketPair.queries L.base L.bits L.originalBits L.lanes L.header L.original
def entries:=DescentResetSourceTicketPair.items L.base L.bits L.originalBits L.lanes L.header L.original
def inputs (w : ℕ) :=ROM.mount (DescentResetSourceTicketPair.pages L.bits L.originalBits L.lanes)
  (DescentResetSourceTicketPair.width L.bits L.originalBits L.lanes) w L.base
def paired (m : Memory w) :=ROM.after (DescentResetSourceTicketPair.pages L.bits L.originalBits L.lanes)
  (DescentResetSourceTicketPair.width L.bits L.originalBits L.lanes) L.base m
def oldPasses:=DescentResetSourceTicketBank.passes L.before L.ticketBase L.originalBits L.bits L.lanes L.hosts L.groups L.questions L.entries
def countProgram (w : ℕ) :=
  (ROM.mount (DescentResetSourceTicketBank.pages L.before L.originalBits L.bits L.lanes)
    (DescentResetSourceTicketBank.span L.originalBits L.lanes) w L.ticketBase).seq (ProtocolRAM.program w L.oldPasses)
def counted (m : Memory w) :=ProtocolRAM.result L.oldPasses (ROM.after (DescentResetSourceTicketBank.pages L.before L.originalBits L.bits L.lanes)
  (DescentResetSourceTicketBank.span L.originalBits L.lanes) L.ticketBase (L.paired m))
def seekProgram (w : ℕ) :=DescentResetSourceSeekRAM.program L.seekBase 4 K L.bits L.originalBits L.bits L.lanes w L.sourceSlot
def searched (m : Memory w) :=DescentResetSourceSeekRAM.memory L.seekBase 4 K L.bits L.originalBits L.bits L.lanes L.sourceSlot (L.counted m)
def localProgram (w : ℕ) :=DescentResetLocalRankRun.program L.rankBase X K L.bits L.lanes L.hosts L.groups w L.header L.ticket
def program (w : ℕ) :=(((L.inputs w).seq (L.countProgram w)).seq (L.seekProgram w)).seq (L.localProgram w)
def memory (m : Memory w) :=DescentResetLocalRankRun.memory L.rankBase X K L.bits L.lanes L.hosts L.groups L.header L.ticket (L.searched m)
def inputTime:=4+10*(6*2^((L.bits*7+L.originalBits)*L.lanes))
def countTime:=(4+10*(2*2^(DescentResetSourceTicketBank.span L.originalBits L.lanes)))+ProtocolRAM.clock L.oldPasses
def seekTime:=(4+10*(K*2*2^((L.bits*7+L.originalBits)*L.lanes)))+
  (4+10*((4*K)*2*2^((DescentResetSourceSeekRAM.keyBits 4 K+L.bits)*L.lanes)))
def localTime:=DescentResetLocalRankRun.time L.rankBase X K L.bits L.lanes L.hosts L.groups L.header L.ticket
def time:=L.inputTime+L.countTime+L.seekTime+L.localTime

theorem ordered : L.base≤L.ticketBase ∧ L.ticketBase≤L.seekBase ∧ L.seekBase≤L.rankBase ∧ L.rankBase≤L.endAddress :=
  ⟨Nat.le_add_right ..,((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..),
    (Nat.le_add_right ..).trans (Nat.le_add_right ..),(Nat.le_add_right ..).trans (DescentResetLocalRankRun.lower ..)⟩

/-- Footprints of the four shared roster, lane and offset banks issued by the previous date. -/
structure Previous (w : ℕ) : Prop where
  header : ∀x j,(L.header x j).Fits w L.base
  original : ∀x j,(L.original x j).Fits w L.base
  ids : ∀i,(L.ports.ids i).Fits w L.base
  idsRoom : ∀i,L.hosts*chunks L.groups L.lanes≤(L.ports.ids i).size
  roster : L.ports.roster.Fits w L.base
  rosterRoom : L.hosts*4≤L.ports.roster.size
  offsets : L.ports.offsets.Fits w L.base
  offRoom : L.hosts≤L.ports.offsets.size
  chunks : L.ports.chunks.Fits w L.base
  chunkRoom : L.hosts*DescentSIMDLookup.chunks L.groups L.lanes≤L.ports.chunks.size

theorem Previous.access {L : Layout X K} (p : L.Previous w) (u : Bank) (end_ : ℕ) (le : L.base≤end_)
    (fit : u.Fits w end_) (rows : L.hosts*DescentSIMDLookup.chunks L.groups L.lanes≤u.size) :
    Accessible L.ports u L.hosts L.groups L.lanes w end_ :=
  ⟨fun j=>⟨(p.ids j).1,(p.ids j).2.1,(p.ids j).2.2.trans le⟩,p.idsRoom,
    ⟨p.roster.1,p.roster.2.1,p.roster.2.2.trans le⟩,p.rosterRoom,
    ⟨p.offsets.1,p.offsets.2.1,p.offsets.2.2.trans le⟩,p.offRoom,
    ⟨p.chunks.1,p.chunks.2.1,p.chunks.2.2.trans le⟩,p.chunkRoom,fit,rows⟩

theorem pull_fits (out : ℕ) (searchOK : ∀j,WordRoom (L.search j) (L.bits*7) L.originalBits L.lanes w out)
    (lookupOK : ∀i,WordRoom (L.lookup i) (DescentResetSourceSeekRAM.keyBits 4 K) L.bits L.lanes w out)
    (p : L.Previous w) (early : L.base≤out) (x : Fin X) (j : Fin K) (cols : Fin K→Bank)
    (access : ∀z,Accessible L.ports (cols z) L.hosts L.groups L.lanes w out) :
    (L.pull x j cols).Fits w out := by
  have query:=(searchOK j).safe _ _ (ProtocolRAMGeneratedWrite.fits_mono _ early (p.header x j))
    (ProtocolRAMGeneratedWrite.fits_mono _ early (p.original x j))
  apply DescentColonies.SplitRAM.fits_total
  intro i
  let c : Fin 4×Fin K:=finProdFinEquiv.symm i
  exact (lookupOK i).safe _ _ query (peer_fits L.ports (cols c.2) out (access c.2) c.1)

theorem any (m : Memory w) (p : L.Previous w) (space : L.endAddress<2^w) :
    (L.program w).Exec m (L.memory m) L.time ∧
    (∀a,a<L.base ∨ L.endAddress≤a→L.memory m a=m a) ∧ CheapCode (L.program w) := by
  obtain ⟨first,second,third,last⟩:=L.ordered
  have rankRoom:=last.trans_lt space
  have seekRoom:=third.trans_lt rankRoom
  have ticketRoom:=second.trans_lt seekRoom
  have init:=DescentResetSourceTicketPair.any L.base L.bits L.originalBits L.lanes w m ticketRoom
  have pairFits:=DescentResetSourceTicketPair.fits L.header L.original p.header p.original ticketRoom
  have counted:=DescentResetSourceTicketBank.any (paid:=L.bits) L.before L.questions L.entries (L.paired m)
    pairFits.1 pairFits.2 seekRoom
  have lookup:=DescentResetSourceSeekRAM.mountBooks L.seekBase L.sourceSlot (L.counted m) rankRoom
  have access (x j) : Accessible L.ports (L.oldBank x j) L.hosts L.groups L.lanes w L.rankBase :=by
    have old:=DescentResetSourceTicketBank.column_fits (w:=w) seekRoom x j
    exact p.access _ _ ((first.trans second).trans third) ⟨old.1,old.2.1,old.2.2.trans third⟩ (DescentDyadicSpan.span_ge _)
  have fits (x j):=(L.pull_fits _ (fun i=>(lookup.2.2.1 i).2) (fun i=>(lookup.2.2.2.1 i).2) p
    ((first.trans second).trans third) x j (L.oldBank x) (access x))
  have done:=DescentResetLocalRankRun.any L.rankBase X K L.bits L.lanes L.hosts L.groups L.header L.ticket (L.searched m)
    (fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ ((first.trans second).trans third) (p.header x j)) fits space
  have countedRun : ((L.inputs w).seq (L.countProgram w)).Exec m (L.counted m)
      (L.inputTime + L.countTime) :=
    @Procedure.Exec.then w (L.inputs w) (L.countProgram w) m (L.paired m) (L.counted m)
      L.inputTime L.countTime (@init.1) (@counted.1)
  have searchedRun : (((L.inputs w).seq (L.countProgram w)).seq (L.seekProgram w)).Exec
      m (L.searched m) (L.inputTime + L.countTime + L.seekTime) :=
    @Procedure.Exec.then w ((L.inputs w).seq (L.countProgram w)) (L.seekProgram w)
      m (L.counted m) (L.searched m) (L.inputTime + L.countTime) L.seekTime
      (@countedRun) (@lookup.1)
  refine ⟨@Procedure.Exec.then w (((L.inputs w).seq (L.countProgram w)).seq (L.seekProgram w))
    (L.localProgram w) m (L.searched m) (L.memory m) (L.inputTime + L.countTime + L.seekTime)
    L.localTime (@searchedRun) (@done.1),?_,?_⟩
  · intro a away
    rcases away with low|high
    · exact (done.2.1 a (.inl (((low.trans_le first).trans_le second).trans_le third))).trans
        ((lookup.2.2.2.2 a (.inl ((low.trans_le first).trans_le second))).trans
          ((counted.2.2 a (.inl (low.trans_le first))).trans (init.2.2.2 a (.inl low))))
    · exact (done.2.1 a (.inr high)).trans ((lookup.2.2.2.2 a (.inr (last.trans high))).trans
        ((counted.2.2 a (.inr ((third.trans last).trans high))).trans (init.2.2.2 a (.inr (((second.trans third).trans last).trans high)))))
  · apply ProtocolRAM.cheap_seq
    · apply ProtocolRAM.cheap_seq
      · apply ProtocolRAM.cheap_seq
        · exact @init.2.1
        · exact @counted.2.1
      · exact @lookup.2.1
    · exact @done.2.2

theorem finalRank_fits (prev : L.Previous w) (space : L.endAddress<2^w) :
    ∀x p j,(L.finalRank x p j).Fits w L.endAddress := by
  intro x p j
  obtain ⟨a,c,f,last⟩:=L.ordered
  have tables:=DescentResetSourceSeekRAM.mountBooks L.seekBase L.sourceSlot (fun _=>0:Memory w) (last.trans_lt space)
  have promote {T : Tables} {v u : ℕ} (fit : WordRoom T v u L.lanes w L.rankBase) : WordRoom T v u L.lanes w L.endAddress :=
    ⟨⟨fit.shift.1,fit.shift.2.1,fit.shift.2.2.trans last⟩,⟨fit.apply.1,fit.apply.2.1,fit.apply.2.2.trans last⟩,fit.shiftBits,fit.applyBits⟩
  have localOK (pos : Fin 3) (z : Fin K) : (L.localBank x pos z).Fits w L.endAddress :=
    DescentResetSignedScan.Ranks.output_fits (DescentResetLocalRankRun.rankBase L.rankBase L.bits L.lanes) x pos z space
  by_cases src : p=2
  · rw [finalRank,ite_eq_left src]
    exact L.pull_fits L.endAddress (fun j=>promote (tables.2.2.1 j).2) (fun i=>promote (tables.2.2.2.1 i).2)
      prev (((a.trans c).trans f).trans last) x j (L.localBank x 0)
      (fun z=>prev.access _ _ (((a.trans c).trans f).trans last) (localOK 0 z) (DescentDyadicSpan.span_ge _))
  · rw [finalRank,ite_eq_right src]
    exact ⟨localOK p j,trivial⟩

end Layout
end
end Hierarchy.DescentResetRankedWindows

end OAI
