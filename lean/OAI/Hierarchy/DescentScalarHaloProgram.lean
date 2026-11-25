import OAI.Hierarchy.DescentScalarHaloPortROM
import OAI.Hierarchy.DescentOrdinaryRootTables
import OAI.Hierarchy.DescentSortedHaloRaster
import OAI.Hierarchy.DescentSortedRosterTariff

namespace OAI
/-! # A sorted four-hop directory and its original walk endpoints in one RAM state -/
namespace Hierarchy.DescentScalarHaloProgram
open DescentSIMDLookup DescentHaloWalkRAM DescentPackedColony DescentRawCablePanel ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (H G M D : ℕ)
local notation "P"=>breadth D
local notation "N"=>H*P

def extent:=2^Nat.clog 2 (H*breadth D)
def statics (base : ℕ):=base+RootTables.length H G M D+extent H D
def endsBase (base : ℕ):=DescentScalarHaloPortROM.stop H G M P (statics H G M D base)
def ranksBase (base : ℕ):=endsBase H G M D base+extent H D
def stop (base : ℕ):=ranksBase H G M D base+extent H D

def ends (base : ℕ):Bank:=⟨endsBase H G M D base,Nat.clog 2 N⟩
def sorted (base : ℕ):Bank:=⟨ranksBase H G M D base,Nat.clog 2 N⟩
def ports (base : ℕ):=DescentScalarHaloPortROM.chart H G M P (statics H G M D base) (sorted H G M D base)
def sortChart (base : ℕ):DescentSortedRoster.Chart:=⟨ends H G M D base,RootTables.bank H D base 5,
  DescentScalarHaloPortROM.slot H G M P (statics H G M D base)⟩

variable (adj : Bank) (base : ℕ)
local notation "root"=>RootTables.walks H D base adj
local notation "stat"=>statics H G M D base
local notation "eo"=>endsBase H G M D base
local notation "rs"=>ranksBase H G M D base
local notation "wc"=>DescentHaloWalkRAM.body root H D 4
local notation "chart"=>sortChart H G M D base
local notation "sc"=>DescentSortedRoster.code chart P H

def program (w : ℕ):=(((RootTables.program H G M D w base).seq (DescentScalarHaloPortROM.program H G M P w stat)).seq (scan w eo N wc)).seq (scan w rs N sc)

def image {w : ℕ} (m : Memory w):=
  let shapes:=DescentScalarHaloPortROM.image H G M P stat (RootTables.image H G M D base m)
  ProtocolRAM.image rs N sc (ProtocolRAM.image eo N wc shapes)

def ticks:=((4+10*RootTables.length H G M D)+(4+10*DescentScalarHaloPortROM.length H G M P))+(4+N*(2*(wc).work+4))+(4+N*(2*(sc).work+4))

def namesTariff : ℕ:=15*(RootTables.length H G M D+1)+15*(DescentScalarHaloPortROM.length H G M P+1)+(11+4*(20*(D+10)^4))+(11+4*(100*(P+1)^3))

theorem resources (w : ℕ) :
    ticks H G M D adj base ≤ ((4+10*RootTables.length H G M D)+(4+10*DescentScalarHaloPortROM.length H G M P))+
      (4+N*(40*(D+10)^4+4))+(4+N*(200*(P+1)^3+4)) ∧
      DescentStaticWordColumn.names (program H G M D adj base w)≤namesTariff H G M D:=by
  have span:=DescentHaloWalkRAM.body_work root H D 4
  have sortWork:=DescentSortedRoster.code_work chart P H
  have a:2*(wc).work+4≤40*(D+10)^4+4:=by omega
  have b:2*(sc).work+4≤200*(P+1)^3+4:=by omega
  constructor
  · dsimp [ticks];have first:=Nat.mul_le_mul_left N a;have second:=Nat.mul_le_mul_left N b;omega
  · dsimp only [program,namesTariff,RootTables.program,DescentScalarHaloPortROM.program]
    simp only [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_scan,DescentStaticWordColumn.names_mount];omega

theorem run {w : ℕ} (peer : Fin H→Fin D→Option (Fin H)) (m : Memory w) (fit : adj.Fits w base) (adjSize : H*D≤adj.size)
    (input : ∀v j,m (adj.base+(v.val*D+j.val))=(number (peer v j):Word w))
    (smallH : H<2^w) (smallD : D<2^w) (smallP : P<2^w) (high : stop H G M D base<2^w) :
    let o:=image H G M D adj base m;let rs_:=Gather.reaching peer;let close:=stop H G M D base;let bank:=ends H G M D base;let io:=ports H G M D base
    (program H G M D adj base w).Exec m o (ticks H G M D adj base) ∧
      Mounted io (DescentSortedRoster.indexed rs_) o G M ∧
      (∀h p,o (bank.base+(h.val*P+p.val))=(number (rs_ h p):Word w)) ∧
      (∀(src:Bank),src.Fits w close→H*chunks G M≤ src.size→Accessible io src H G M w close) ∧
      bank.Fits w close ∧ N≤bank.size ∧ (∀j,j<base ∨ close≤j → o j=m j) ∧ CheapCode (program H G M D adj base w):=by
  intro o rs_ close bank io
  have capacity:N≤extent H D:=Nat.le_pow_clog (by decide) _
  have bRoot:base+RootTables.length H G M D≤ stat:=Nat.le_add_right ..
  have eShape:stat+DescentScalarHaloPortROM.length H G M P≤eo:=Nat.le_add_right ..
  have shapeCut:stat≤eo:=(Nat.le_add_right ..).trans eShape
  have endCut:eo+N≤rs:=Nat.add_le_add_left capacity _
  have sortCut:rs+N≤close:=Nat.add_le_add_left capacity _
  have begin:base≤ stat:=(Nat.le_add_right ..).trans bRoot
  have order:eo≤rs:=Nat.le_add_right ..;have last:rs≤close:=Nat.le_add_right ..
  let rootState:=RootTables.image H G M D base m
  let st:=DescentScalarHaloPortROM.image H G M P stat rootState
  let m1:=ProtocolRAM.image eo N wc st
  have rootRun:=RootTables.mount H G M D base m (bRoot.trans_lt (shapeCut.trans_lt (order.trans_lt (last.trans_lt high))))
  have shapeRun:=DescentScalarHaloPortROM.mount H G M P stat (sorted H G M D base) rootState (eShape.trans_lt (order.trans_lt (last.trans_lt high)))
  have rootMem:=RootTables.keep H G M D rootRun.2.1 (fun x upper=>shapeRun.2.2.1 _ (.inl (upper.trans_le bRoot)))
  have moved (b:Bank) (h:b.Fits w base):b.Fits w eo:=⟨h.1,h.2.1,h.2.2.trans (begin.trans shapeCut)⟩
  have made {B:Bank} (endAt:B.base+B.size≤eo):B.Fits w eo:=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (endAt.trans_lt (order.trans_lt (last.trans_lt high))),endAt⟩
  have fieldFits (s:Fin 6) : (RootTables.bank H D base s.val).Fits w eo:=by
    apply made;have bound:=Nat.mul_le_mul_right N s.isLt.le
    change base+s.val*N+extent H D≤eo;apply le_trans _ shapeCut;dsimp [statics,RootTables.length];omega
  have addr (h:Fin H) (j:Fin D) : h.val*D+j.val<H*D:=(Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ h.isLt)
  have a0 (h:Fin H) (j:Fin D):st (adj.base+(h.val*D+j.val))=(number (peer h j):Word w):=by
    have pos:adj.base+(h.val*D+j.val)<base:=(Nat.add_lt_add_left ((addr h j).trans_le adjSize) _).trans_le fit.2.2
    exact (shapeRun.2.2.1 _ (.inl (pos.trans_le begin))).trans ((rootRun.2.2.1 _ (.inl pos)).trans (input h j))
  have data_:=RootTables.row_data H G M D base peer adj st rootMem a0
  have walkFits:DescentHaloWalkRAM.Fits root eo H D w:=⟨moved _ fit,fieldFits 0,fun i=>fieldFits ⟨i.val+1,by omega⟩,adjSize,capacity,fun _=>capacity,
    endCut.trans_lt (last.trans_lt high),smallH,smallD⟩
  obtain ⟨walkRun,walkWords,walkCheap⟩:=DescentHaloWalkRAM.run root eo walkFits peer st data_.1
  have keep0 (x:ℕ) (h:x<eo):m1 x=st x:=ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl h)
  have preserve (b:Bank) (f:b.Fits w eo):b.Fits w rs:=⟨f.1,f.2.1,f.2.2.trans order⟩
  have endGood : bank.Fits w rs:=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (last.trans_lt high),le_rfl⟩
  have rankGood : (sorted H G M D base).Fits w close:=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt high,le_rfl⟩
  obtain ⟨ids,offsets,chunks_,slotF,slotS⟩:=DescentScalarHaloPortROM.statics H G M P stat eo (sorted H G M D base) le_rfl (order.trans_lt (last.trans_lt high))
  have sFit : DescentSortedRoster.Room chart P H w rs:=by
    refine ⟨?_,smallH,smallP,sortCut.trans_lt high⟩
    intro b s;rcases List.mem_cons.mp s with rfl|s
    · exact ⟨endGood,capacity⟩
    rcases List.mem_cons.mp s with rfl|s
    · exact ⟨preserve _ (fieldFits 5),capacity⟩
    rcases List.mem_cons.mp s with rfl|s
    · exact ⟨preserve _ slotF,slotS⟩
    · contradiction
  have range (h:Fin H) (p:Fin P) : h.val*P+p.val<N:=(Nat.add_lt_add_left p.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ h.isLt)
  have subscript (h:Fin H) (p:Fin P) : (DescentHaloWalkRAM.row h p).val=h.val*P+p.val:=by simp [DescentHaloWalkRAM.row,finProdFinEquiv_apply_val];ring
  have actual:DescentSortedRoster.Raw chart rs_ m1:=by
    refine ⟨?_,?_,?_⟩
    · intro h p;apply (keep0 _ ((Nat.add_lt_add_left ((range h p).trans_le capacity) _).trans_le (fieldFits 5).2.2)).trans
      simpa [Ranks.id,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using data_.2.1 h p
    · intro h p;exact (keep0 _ ((Nat.add_lt_add_left ((range h p).trans_le slotS) _).trans_le slotF.2.2)).trans (shapeRun.2.1.slots h p)
    · intro h p
      change ProtocolRAM.image eo N wc st (eo+(h.val*P+p.val)) = (number (walk peer h (path p) 4):Word w)
      simpa only [subscript] using walkWords h p
  obtain ⟨sortRun,rankWord,_⟩:=DescentSortedRoster.issued chart rs_ m1 rs sFit actual
  have keep (x:ℕ) (h:x<eo):o x=st x:=(ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (h.trans_le order))).trans (keep0 x h)
  have table (src:Bank) (sf:src.Fits w close) (span:H*chunks G M≤ src.size):=DescentScalarHaloPortROM.geometry H G M P stat close (sorted H G M D base) src (order.trans last) high rankGood capacity sf span
  let rootCPU := RootTables.program H G M D w base
  let shapeCPU := DescentScalarHaloPortROM.program H G M P w stat
  let walkCPU := scan w eo N wc
  let sortCPU := scan w rs N sc
  let rootTicks := 4+10*RootTables.length H G M D
  let shapeTicks := 4+10*DescentScalarHaloPortROM.length H G M P
  let walkTicks := 4+N*(2*(wc).work+4)
  let sortTicks := 4+N*(2*(sc).work+4)
  have rootsRun : (rootCPU.seq shapeCPU).Exec m st (rootTicks+shapeTicks) :=
    @Procedure.Exec.then w rootCPU shapeCPU m rootState st rootTicks shapeTicks rootRun.1 shapeRun.1
  have walksRun : ((rootCPU.seq shapeCPU).seq walkCPU).Exec m m1 (rootTicks+shapeTicks+walkTicks) :=
    @Procedure.Exec.then w (rootCPU.seq shapeCPU) walkCPU m st m1 (rootTicks+shapeTicks) walkTicks rootsRun walkRun
  have ran : (program H G M D adj base w).Exec m o (ticks H G M D adj base) :=
    @Procedure.Exec.then w ((rootCPU.seq shapeCPU).seq walkCPU) sortCPU m m1 o (rootTicks+shapeTicks+walkTicks) sortTicks walksRun sortRun
  have cheap : CheapCode (program H G M D adj base w) :=
    @cheap_seq w ((rootCPU.seq shapeCPU).seq walkCPU) sortCPU
      (@cheap_seq w (rootCPU.seq shapeCPU) walkCPU
        (@cheap_seq w rootCPU shapeCPU rootRun.2.2.2 shapeRun.2.2.2) walkCheap)
      (@DescentSortedRoster.cheap_code chart P H w rs)
  refine ⟨@ran,⟨?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,@cheap⟩
  · intro p s;exact (keep _ ((Nat.add_lt_add_left ((DescentSIMDLookup.row H G M p).isLt.trans_le ((ids s).2)) _).trans_le (ids s).1.2.2)).trans (shapeRun.2.1.ids s p)
  · exact rankWord
  · intro h;exact (keep _ ((Nat.add_lt_add_left (h.isLt.trans_le offsets.2) _).trans_le offsets.1.2.2)).trans (shapeRun.2.1.offsets h)
  · intro p;exact (keep _ ((Nat.add_lt_add_left ((DescentSIMDLookup.row H G M p).isLt.trans_le chunks_.2) _).trans_le chunks_.1.2.2)).trans (shapeRun.2.1.chunks p)
  · intro h p;exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl ((Nat.add_lt_add_left (range h p) _).trans_le endCut))).trans (by change ProtocolRAM.image eo N wc st (eo+(h.val*P+p.val)) = (number (walk peer h (path p) 4):Word w); simpa only [subscript] using walkWords h p)
  · exact fun src sf lim=>(table src sf lim).1
  · exact ⟨endGood.1,endGood.2.1,endGood.2.2.trans last⟩
  · exact capacity
  · intro j outside;rcases outside with lo|hi
    · exact (keep _ (lo.trans_le (begin.trans shapeCut))).trans ((shapeRun.2.2.1 _ (.inl (lo.trans_le begin))).trans (rootRun.2.2.1 _ (.inl lo)))
    · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr (sortCut.trans hi))).trans ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr (endCut.trans (last.trans hi)))).trans ((shapeRun.2.2.1 _ (.inr (eShape.trans (order.trans (last.trans hi))))).trans (rootRun.2.2.1 _ (.inr (bRoot.trans (shapeCut.trans (order.trans (last.trans hi))))))))

end
end Hierarchy.DescentScalarHaloProgram

end OAI
