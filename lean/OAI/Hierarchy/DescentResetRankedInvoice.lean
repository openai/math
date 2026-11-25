import OAI.Hierarchy.DescentResetRankedWindows
import OAI.Hierarchy.DescentNextSignedAll
import OAI.Hierarchy.DescentResetWindowTail

namespace OAI
/-! # Numerical work and hardware charges of measured reset prefix and signed passes -/
namespace Hierarchy.DescentResetRankedWindows.Layout
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentOrdinaryAtomFieldRAM
open DescentResetSignedScan DescentPackedFlowBatch DescentColonies.SplitRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical
noncomputable section
variable {X K w : ℕ} (L : Layout X K)

def pairWork (lim : ℕ):=2*lim+11
def pullWork (K lim : ℕ):=1+4*K*(pairWork lim+64)
def keyWork (K lim : ℕ):=lim+pullWork K lim+11
def prefixWork (K lim : ℕ):=1+K*(2*keyWork K lim+12)
def finalWork (K lim : ℕ):=max 7 (pullWork K lim)
def originalWork (K lim : ℕ):=DescentResetSourceTicketBank.expressionCost K (pairWork lim)
def rawWords:=6*2^(DescentResetSourceTicketPair.width L.bits L.originalBits L.lanes)
def ticketWords:=2*2^(DescentResetSourceTicketBank.span L.originalBits L.lanes)
def searchWords:=K*2*2^((L.bits*7+L.originalBits)*L.lanes)
def returnWords:=(4*K)*2*2^((DescentResetSourceSeekRAM.keyBits 4 K+L.bits)*L.lanes)
def keyWords:=2*2^(RankInput.width L.bits L.lanes)
def prefixWords:=Ranks.headWords L.bits L.lanes

def scans (n rows u : ℕ) :=4+n*(4+rows*(2*u+4))
def scanNames (n u : ℕ) :=15+n*(11+4*u)
def clockBudget (lim : ℕ):=
  L.inputTime+((4+10*L.ticketWords)+scans (X*K) (L.hosts*chunks L.groups L.lanes) (originalWork K lim))+L.seekTime+
    ((4+10*L.keyWords)+((4+10*L.prefixWords)+scans (Ranks.count X K) (L.hosts*chunks L.groups L.lanes) (prefixWork K lim)))
def textBudget (lim : ℕ):=
  15*(L.rawWords+1)+(15*(L.ticketWords+1)+scanNames (X*K) (originalWork K lim))+
  (15*(L.searchWords+1)+15*(L.returnWords+1))+
  (15*(L.keyWords+1)+(15*(L.prefixWords+1)+scanNames (Ranks.count X K) (prefixWork K lim)))

variable (lim : ℕ) (headers : ∀x j,(L.header x j).work≤lim) (words : ∀x j,(L.original x j).work≤lim)
include headers words

theorem source_work (x : Fin X) (j : Fin K) (prior : Fin K→Bank) : (L.pull x j prior).work≤pullWork K lim :=by
  have query : ((L.search j).read (L.header x j) (L.original x j)).work≤pairWork lim:=by
    rw [DescentPackedZip.work]
    have :=headers x j;have :=words x j
    unfold pairWork;omega
  exact (DescentResetSourcePullRAM.work ..).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right query 64)) 1)

theorem final_work (x : Fin X) (a : Fin 3) (j : Fin K) : (L.finalRank x a j).work≤finalWork K lim :=by
  unfold finalRank
  split
  · exact (source_work L lim headers words x j _).trans (Nat.le_max_right ..)
  · exact Nat.le_max_left ..

private theorem key_work (x : Fin X) (j : Fin K) :
    (RankInput.expr L.rankBase L.bits L.lanes (L.header x j) (L.ticket x j)).work≤keyWork K lim :=by
  unfold RankInput.expr
  rw [DescentPackedZip.work]
  exact Nat.add_le_add_right (Nat.add_le_add (headers x j) (source_work L lim headers words x j _)) _

theorem invoice :
    L.time≤L.clockBudget lim ∧ DescentStaticWordColumn.names (L.program w)≤L.textBudget lim :=by
  let N:=L.hosts*chunks L.groups L.lanes
  let q:=DescentResetLocalRankRun.query L.rankBase L.bits L.lanes L.header L.ticket
  let a:=DescentResetLocalRankRun.items L.rankBase L.bits L.lanes L.header L.ticket
  let start:=DescentResetLocalRankRun.rankBase L.rankBase L.bits L.lanes
  let arg:=pairWork lim
  have inWork (r : Fin 3) (x : Fin X) (j : Fin K) :
      (DescentResetSourceTicketPair.expression L.base L.bits L.originalBits L.lanes r (L.header x j) (L.original x j)).work≤arg :=by
    rw [DescentResetSourceTicketPair.work]
    have h:=headers x j;have o:=words x j
    dsimp [arg,pairWork];omega
  have qCost x j : (L.questions x j).work≤arg:=inWork 0 x j
  have itemsCost (x : Fin X) (i : Fin (K+K)) : (L.entries x i).work≤arg:=by
    refine Fin.addCases (motive:=fun i=>(L.entries x i).work≤arg) ?_ ?_ i
    · intro j;simpa [entries,DescentResetSourceTicketPair.items] using inWork 1 x j
    · intro j;simpa only [entries,DescentResetSourceTicketPair.items,Fin.addCases_right] using inWork 2 x j
  have charged:=DescentResetSourceTicketBank.tariff (w:=w) (H:=L.hosts) (G:=L.groups) (M:=L.lanes) (root:=L.ticketBase)
    (b:=L.originalBits) (paid:=L.bits) L.before L.questions L.entries arg qCost itemsCost
  have qBound (x p j) : (q x p j).work≤keyWork K lim:=key_work L lim headers words x j
  have aBound (x p j i) : (a x p j i).work≤keyWork K lim:=key_work L lim headers words x i
  have pref:=Ranks.clock_bound (b:=L.bits) (paid:=L.bits) (M:=L.lanes) (H:=L.hosts) (G:=L.groups) start q a
    (keyWork K lim) qBound aBound
  constructor
  · exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_left charged.1 _) _) _)
      (Nat.add_le_add_left pref _)
  · have bodyCost j (active : j<Ranks.count X K) :
        (Ranks.expression L.bits L.bits L.lanes start q a j).work≤prefixWork K lim:=by
      obtain ⟨⟨⟨x,p⟩,i⟩,hit⟩:=(Ranks.order X K).surjective ⟨j,active⟩
      rw [←show ((Ranks.order X K) ((x,p),i)).val=j from congrArg Fin.val hit,Ranks.at_query]
      let tab:=Ranks.tables L.bits L.bits L.lanes start (Ranks.parallelQuery p)
      have cost (r : Fin K) : (tab.read (q x p i) (a x p i r)).work≤2*keyWork K lim+11:=by
        rw [DescentPackedZip.work];have:=qBound x p i;have:=aBound x p i r;omega
      simpa [Ranks.body,tab,prefixWork,List.length_finRange,Nat.add_assoc] using work_total _ _ cost (List.finRange K)
    have seqNames:=DescentNextSignedWindow.Native.All.sweep_names (w:=w) (Ranks.start start L.bits L.lanes) N (DescentDyadicSpan.span N) 0
      (Ranks.count X K) (Ranks.expression L.bits L.bits L.lanes start q a) (prefixWork K lim) (by
        intro j _ h;exact bodyCost j (by simpa using h))
    have countNames : DescentStaticWordColumn.names (L.countProgram w)≤15*(L.ticketWords+1)+scanNames (X*K) (originalWork K lim):=charged.2
    have named : DescentStaticWordColumn.names (L.localProgram w)≤15*(L.keyWords+1)+(15*(L.prefixWords+1)+scanNames (Ranks.count X K) (prefixWork K lim)):=by
      unfold localProgram DescentResetLocalRankRun.program RankInput.program Ranks.program
      rw [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_seq]
      simp only [ROM.mount,DescentStaticWordColumn.names_mount]
      exact Nat.add_le_add_left (Nat.add_le_add_left seqNames _) _
    rw [program,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_seq]
    have st:DescentStaticWordColumn.names (L.seekProgram w)=15*(L.searchWords+1)+15*(L.returnWords+1):=DescentResetSourceSeekRAM.names ..
    have init:DescentStaticWordColumn.names (L.inputs w)=15*(L.rawWords+1):=DescentStaticWordColumn.names_mount ..
    rw [st,init]
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_left countNames _) _) named

def signedFieldWork (K lim : ℕ):=lim+finalWork K lim+11

theorem signed_field_work {z : ℕ} (x : Fin X) (a : Fin (2*K)) (f : Fin 8) :
    (DescentResetFieldAssembler.fields z L.bits L.lanes L.header L.finalRank x a f).work ≤ signedFieldWork K lim :=by
  obtain ⟨⟨side,j⟩,at_⟩:=finProdFinEquiv.surjective a
  subst a
  simp only [DescentResetFieldAssembler.fields,Equiv.symm_apply_apply,DescentPackedZip.work]
  exact Nat.add_le_add_right (Nat.add_le_add (headers x j) (final_work L lim headers words x _ j)) _

def signedTermWork (K lim : ℕ) :=1+2*K*(14+8*(signedFieldWork K lim+11))
def tailClock (cap lim : ℕ):=4+10*(32*2^(DescentResetFieldAssembler.width L.bits L.lanes))+
  ((4+10*DescentNextSignedWindow.Native.All.headWords cap L.bits L.lanes)+
    scans (DescentNextSignedWindow.Native.All.count X cap) (L.hosts*chunks L.groups L.lanes) (signedTermWork K lim))
def tailText (cap lim : ℕ):=15*(32*2^(DescentResetFieldAssembler.width L.bits L.lanes)+1)+
  (15*(DescentNextSignedWindow.Native.All.headWords cap L.bits L.lanes+1)+15+
    DescentNextSignedWindow.Native.All.count X cap*(11+4*signedTermWork K lim))

theorem tail_invoice (D cap : ℕ) :
    DescentResetWindowTail.time L.endAddress X D cap L.bits L.lanes L.hosts L.groups L.header L.finalRank≤L.tailClock cap lim ∧
    DescentStaticWordColumn.names (DescentResetWindowTail.program L.endAddress X D cap L.bits L.lanes L.hosts L.groups w L.header L.finalRank)≤
      L.tailText cap lim :=by
  let e:=DescentResetWindowTail.fields L.endAddress L.bits L.lanes cap L.header L.finalRank
  let start:=DescentResetWindowTail.next L.endAddress L.bits L.lanes
  have bound (x slot a f) : (e x slot a f).work ≤ signedFieldWork K lim:=signed_field_work L lim headers words x a f
  constructor
  · apply Nat.add_le_add_left
    exact DescentNextSignedWindow.Native.All.clock_bound (D:=D) (H:=L.hosts) (G:=L.groups) start e _ bound
  · rw [DescentResetWindowTail.program,DescentStaticWordColumn.names_seq]
    have first : DescentStaticWordColumn.names (DescentResetFieldAssembler.program L.endAddress L.bits L.lanes w)=
        15*(32*2^(DescentResetFieldAssembler.width L.bits L.lanes)+1):=DescentStaticWordColumn.names_mount ..
    rw [first]
    apply Nat.add_le_add_left
    exact DescentNextSignedWindow.Native.All.text_bound (D:=D) (H:=L.hosts) (G:=L.groups) start e _ bound

end
end Hierarchy.DescentResetRankedWindows.Layout

end OAI
