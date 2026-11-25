import OAI.Hierarchy.DescentScalarHaloProgram

namespace OAI
namespace Hierarchy.DescentScalarHaloProgram
open DescentSIMDLookup DescentHaloWalkRAM DescentPackedColony DescentRawCablePanel ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (H G M D : ℕ)
local notation "P"=>breadth D
local notation "N"=>H*P

variable (adj : Bank) (base : ℕ)
local notation "root"=>RootTables.walks H D base adj
local notation "stat"=>statics H G M D base
local notation "eo"=>endsBase H G M D base
local notation "rs"=>ranksBase H G M D base
local notation "wc"=>DescentHaloWalkRAM.body root H D 4
local notation "chart"=>sortChart H G M D base
local notation "sc"=>DescentSortedRoster.code chart P H

/-- The four public scans terminate at their fixed addresses for every incoming tape. -/
theorem any {w : ℕ} (m : Memory w) (fit : adj.Fits w base) (adjSize : H*D≤adj.size)
    (smallH : H<2^w) (smallD : D<2^w) (smallP : P<2^w) (high : stop H G M D base<2^w) :
    let o:=image H G M D adj base m; let close:=stop H G M D base; let bank:=ends H G M D base; let io:=ports H G M D base
    (program H G M D adj base w).Exec m o (ticks H G M D adj base) ∧
    (∀src : Bank, src.Fits w close→H*chunks G M≤ src.size→Accessible io src H G M w close) ∧
    bank.Fits w close ∧ N≤bank.size ∧ (∀j,j<base ∨ close≤j → o j=m j) ∧ CheapCode (program H G M D adj base w) :=by
  intro o close bank io
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
  have moved (b:Bank) (h:b.Fits w base):b.Fits w eo:=⟨h.1,h.2.1,h.2.2.trans (begin.trans shapeCut)⟩
  have made {B:Bank} (endAt:B.base+B.size≤eo):B.Fits w eo:=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (endAt.trans_lt (order.trans_lt (last.trans_lt high))),endAt⟩
  have fieldFits (s:Fin 6) : (RootTables.bank H D base s.val).Fits w eo:=by
    apply made;have bound:=Nat.mul_le_mul_right N s.isLt.le
    change base+s.val*N+extent H D≤eo;apply le_trans _ shapeCut;dsimp [statics,RootTables.length];omega
  have walkFits:DescentHaloWalkRAM.Fits root eo H D w:=⟨moved _ fit,fieldFits 0,fun i=>fieldFits ⟨i.val+1,by omega⟩,adjSize,capacity,fun _=>capacity,
    endCut.trans_lt (last.trans_lt high),smallH,smallD⟩
  have walkRun : (scan w eo N wc).Exec st m1 (4+N*(2*(wc).work+4)) :=
    @scan_exec w eo N wc st (DescentHaloWalkRAM.body_fits root eo walkFits 4) walkFits.outside
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
  have sortRun : (scan w rs N sc).Exec m1 o (4+N*(2*(sc).work+4)) :=
    @scan_exec w rs N sc m1 (DescentSortedRoster.built_fits chart rs sFit) (sortCut.trans_lt high)
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
        (@cheap_seq w rootCPU shapeCPU rootRun.2.2.2 shapeRun.2.2.2) (@scan_cheap w eo N wc))
      (@DescentSortedRoster.cheap_code chart P H w rs)
  refine ⟨@ran,?_,?_,?_,?_,@cheap⟩
  · exact fun src sf lim=>(table src sf lim).1
  · exact ⟨endGood.1,endGood.2.1,endGood.2.2.trans last⟩
  · exact capacity
  · intro j outside;rcases outside with lo|hi
    · exact (keep _ (lo.trans_le (begin.trans shapeCut))).trans ((shapeRun.2.2.1 _ (.inl (lo.trans_le begin))).trans (rootRun.2.2.1 _ (.inl lo)))
    · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr (sortCut.trans hi))).trans ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr (endCut.trans (last.trans hi)))).trans ((shapeRun.2.2.1 _ (.inr (eShape.trans (order.trans (last.trans hi))))).trans (rootRun.2.2.1 _ (.inr (bRoot.trans (shapeCut.trans (order.trans (last.trans hi))))))))

end
end Hierarchy.DescentScalarHaloProgram

end OAI
