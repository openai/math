import OAI.ThreeFlat.RAM.HistoryShrinkSiteExecution
import OAI.ThreeFlat.RAM.HistoryShrinkCharges
import OAI.ThreeFlat.RAM.HistoryShrinkPartyRecords

namespace OAI
set_option quotPrecheck false
set_option maxErrors 600

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickWorkspace HistoryStageBody.Physical
open HistoryRefreshEmitter HistoryGatherBody HistoryGatherExecution HistoryScratch
open scoped Classical Fin.CommRing
noncomputable section
variable {u : ℕ}
local notation "W" => (16*u^10)
local notation "V" => volume u

/-- Reads retained above the selected S17 buffer, in native word arithmetic. -/
structure PartyReads (u : ℕ) (J : HistoryGatherBody.Layout) (m : Memory W) (page : ℕ) : Prop where
  cursor : base u 18≤((J.nodePorts.cursor:Word W)).val
  node : base u 18≤(nodeWord J m+5).val
  kernel : ∀j:Fin 5,base u 18≤((selected J m).kernel+(j.val:Word W)).val
  incident : ∀j:Fin 6,base u 18≤((selected J m).incident+(j.val:Word W)).val
  kind : ∀j:Fin 7,base u 18≤((selected J m).kindPage+(j.val:Word W)).val
  page : base u 18≤page

/-- The selected gather can write its S17 source rows and its S12 bit map while
keeping every input to the selected party decoder outside both output ranges. -/
structure PartySpace (u : ℕ) (J : HistoryGatherBody.Layout) (m : Memory W) (node page size : ℕ) : Prop where
  positive : 0<J.party.V
  resident : portsEnd J<2^W
  hSize : 3+5*J.demandCap+4*J.supplyCap≤J.party.V
  stop : portsEnd J≤base u 18
  mapBase : ((selected J m).privatePage 2).val=HistoryPartyPair.atPair J.party node 2
  fitsAddress : HistoryPartyPair.atPair J.party node 2<2^W
  atNode : (HistoryNodePorts.id J.nodePorts).value (fun _=>0) m (fun _=>0)=(node:Word W)
  pairInfo : ((selected J m).privatePage 1+1).val<J.temp
  mapRoom : ((selected J m).privatePage 2).val+size<2^W
  range : portsEnd J≤((selected J m).privatePage 2).val ∨ ((selected J m).privatePage 2).val+size≤J.temp
  keep : ∀a,let sel:=selected J m
    a=(J.nodePorts.cursor:Word W).val ∨ a=(nodeWord J m+5).val ∨ a=(sel.kernel+4).val ∨
    a=(sel.incident+2).val ∨ a=(sel.incident+3).val ∨
    (∃i:Fin 7,a=(sel.kindPage+(i.val:Word W)).val) ∨
    (page≤a ∧ a<page+HistoryPortCatalogue.stride J.demandCap J.supplyCap J.digitCap) →
    (a<J.temp ∨ portsEnd J≤a) ∧ (a<((selected J m).privatePage 2).val ∨ ((selected J m).privatePage 2).val+size≤a)
  clear : let last:=page+HistoryPortCatalogue.stride J.demandCap J.supplyCap J.digitCap
    (last≤J.temp ∨ portsEnd J≤page) ∧ (last≤((selected J m).privatePage 2).val ∨ ((selected J m).privatePage 2).val+size≤page)
  headAt : page+HistoryPortCatalogue.headerBase J.demandCap J.supplyCap<2^W
  mapEnd : HistoryPartyPair.atPair J.party node 2+J.party.V≤J.temp
  enough : 4≤J.party.V

variable {J : HistoryGatherBody.Layout} {m : Memory (16*u^10)} {node page size : ℕ}

private theorem nextPair (bank : ℕ) :
    HistoryPartyPair.atPair J.party node bank+J.party.V=HistoryPartyPair.atPair J.party node (bank+1) := by
  unfold HistoryPartyPair.atPair HistoryScratch.atWord HistoryScratch.sector
  ring

private theorem selected_pair_word {width : ℕ} (layout : HistoryGatherBody.Layout)
    (mem : Memory width) (n bank : ℕ)
    (atNode : (HistoryNodePorts.id layout.nodePorts).value (fun _ => 0) mem (fun _ => 0) = (n : Word width)) :
    (HistoryGatherBody.selected layout mem).privatePage bank =
      (HistoryPartyPair.atPair layout.party n bank : Word width) := by
  simp [HistoryGatherBody.selected, HistoryPartyPair.atPair, HistoryScratch.atWord, atNode,
    Nat.cast_add, Nat.cast_mul]

theorem PartySpace.of_banks (b : PhysicalBanks u J) (age : 16≤u) (small : node<V^2)
    (motif : J.party.motif<J.party.motifs) (party : J.party.party<J.party.parties)
    (capacity : (J.party.motifs+2)*(J.party.parties+2)*8*32≤V)
    (header : 3+5*J.demandCap+4*J.supplyCap≤V) (length : size≤V)
    (live : PartyReads u J m page)
    (headRoom : page+HistoryPortCatalogue.headerBase J.demandCap J.supplyCap<2^W)
    (nodeValue : (HistoryNodePorts.id J.nodePorts).value (fun _=>0) m (fun _=>0)=(node:Word W)) :
    PartySpace u J m node page size := by
  have big : 1024≤V:=Nat.pow_le_pow_right (by decide : 0<2)
    ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have pow : V≤V^4:=Nat.le_self_pow (by decide) _
  have stop : portsEnd J≤base u 18 := by
    have ticks:=Nat.mul_le_mul_right V (show 1+J.demandCap+J.supplyCap≤V by omega)
    have growth:V^2≤V^4:=Nat.pow_le_pow_right (Nat.two_pow_pos _) (by decide)
    rw [pow_two] at growth
    have high:=apart (u:=u) (by decide : 17<18)
    unfold portsEnd;rw [b.gather,b.wordCount]
    change base u 17+V^4≤base u 18 at high
    omega
  have ctrl:=word_space (u:=u) (i:=18) (by omega) (by change 18<V^4;omega)
  let bank : Local:=⟨J.party.motif+2,J.party.party+2,2,2⟩
  have valid : bank.Valid J.party.motifs J.party.parties :=
    ⟨Nat.add_lt_add_right motif 2, Nat.add_lt_add_right party 2,
      (by decide : 2 < 8), (by decide : 2 < 32)⟩
  have last:=HistoryScratch.fits (base:=base u 12) small capacity valid (by omega : V-1<V)
  have top : HistoryPartyPair.atPair J.party node 2+V≤base u 12+stride u := by
    have eq : atWord (base u 12) V J.party.motifs J.party.parties node bank (V-1)=
        HistoryPartyPair.atPair J.party node 2+(V-1) := by
      simp [atWord,HistoryPartyPair.atPair,bank,b.arena,b.wordCount]
    rw [eq] at last
    change _≤base u 12+V^4
    omega
  have mapEnd := top.trans (apart (u:=u) (by decide : 12<17))
  have early:=apart (u:=u) (by decide : 17<18)
  have fit : HistoryPartyPair.atPair J.party node 2<2^W := by omega
  have pointer:=HistoryRefreshEmitter.private_map_base J node m nodeValue fit
  have endMap : ((selected J m).privatePage 2).val+size≤base u 17 := by rw [pointer];omega
  have prev := nextPair (J:=J) (node:=node) 1
  change HistoryPartyPair.atPair J.party node 1+J.party.V=HistoryPartyPair.atPair J.party node 2 at prev
  have summary := selected_pair_word J m node 1 nodeValue
  have info : HistoryPartyPair.atPair J.party node 1+1<base u 17 := by rw [b.wordCount] at prev;omega
  have summaryFit : HistoryPartyPair.atPair J.party node 1+1<2^W := by omega
  refine ⟨by rw [b.wordCount];omega,by omega,(by rw [b.wordCount];exact header),stop,pointer,fit,nodeValue,?_,by omega,
    .inr (by rw [b.gather];exact endMap),?_,?_,?_,?_,by rw [b.wordCount];omega⟩
  · rw [summary,b.gather,←Nat.cast_one (R:=Word W),←Nat.cast_add,Fin.val_cast_of_lt summaryFit]
    exact info
  · intro a
    dsimp only
    intro touched
    have high : base u 18≤a := by
      rcases touched with rfl|rfl|rfl|rfl|rfl|⟨i,rfl⟩|inside
      · exact live.cursor
      · exact live.node
      · exact live.kernel 4
      · exact live.incident 2
      · exact live.incident 3
      · exact live.kind i
      · exact live.page.trans inside.1
    exact ⟨.inr (stop.trans high),.inr (by omega)⟩
  · exact ⟨.inr (stop.trans live.page),.inr (by have:=live.page;omega)⟩
  · exact headRoom
  · rwa [b.wordCount,b.gather]

theorem PartySpace.mapCount (R : PartySpace u J m node page size) (active : partyActive J m)
    (info : m (HistoryPartyPair.atPair J.party node 1+1)=(size:Word W)) :
    (partyMapCount J m).val=size := by
  have summary := selected_pair_word J m node 1 R.atNode
  have prev:=nextPair (J:=J) (node:=node) 1
  have result:=R.fitsAddress
  have four:=R.enough
  change HistoryPartyPair.atPair J.party node 1+J.party.V=HistoryPartyPair.atPair J.party node 2 at prev
  have fit : HistoryPartyPair.atPair J.party node 1+1<2^W := by omega
  have sz : size<2^W := by have:=R.mapRoom;omega
  have address : ((HistoryGatherBody.selected J m).privatePage 1+((1:ℕ):Word W)).val =
      HistoryPartyPair.atPair J.party node 1+1 := by
    rw [summary,←Nat.cast_add,Fin.val_cast_of_lt fit]
  have read : wordAt m ((selected J m).privatePage 1) 1 = (size : Word W) := by
    change m ((HistoryGatherBody.selected J m).privatePage 1+((1:ℕ):Word W)).val = _
    rw [address, info]
  have chosen : partyMapCount J m = wordAt m ((selected J m).privatePage 1) 1 := by
    unfold HistoryGatherBody.partyMapCount
    exact ite_eq_left active
  exact (congrArg Fin.val (chosen.trans read)).trans (Fin.val_cast_of_lt sz)

theorem PartySpace.clearPair (R : PartySpace u J m node page size) (plan : Plan W)
    (whereMap : plan.gatherBase=HistoryPartyPair.atPair J.party node 2)
    (cells : ℕ) (rows : 4*cells≤J.party.V) :
    ∀ a,(HistoryPartyPair.atPair J.party node 0≤a ∧ a<HistoryPartyPair.atPair J.party node 0+4*cells) ∨
      (HistoryPartyPair.atPair J.party node 1≤a ∧ a<HistoryPartyPair.atPair J.party node 1+4) →
      (a<J.temp ∨ J.temp+(@HistoryGatherBody.fields W J).length≤a) ∧
      (∀q j,j<cap J q → a<srcBase J q j ∨ srcBase J q j+plan.width q j≤a) ∧
      (a<plan.gatherBase ∨ plan.gatherBase+plan.gatherCount≤a) := by
  intro a live
  have x:=nextPair (J:=J) (node:=node) 0
  have y:=nextPair (J:=J) (node:=node) 1
  change HistoryPartyPair.atPair J.party node 0+J.party.V=HistoryPartyPair.atPair J.party node 1 at x
  change HistoryPartyPair.atPair J.party node 1+J.party.V=HistoryPartyPair.atPair J.party node 2 at y
  have f:=R.enough
  have early : a<HistoryPartyPair.atPair J.party node 2 := by rcases live with v|v <;>omega
  have last:=R.mapEnd
  exact ⟨.inl (by omega),fun q j _=>.inl (by unfold srcBase;omega),.inl (by rwa [whereMap])⟩

end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickWorkspace HistoryStageBody.Physical HistoryRefreshEmitter
open HistoryGatherBody HistoryGatherExecution HistoryScratch BitLayout
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {u : ℕ}
local notation "W" => (16*u^10)
local notation "V" => volume u

/-- Lift the retained kernel/incident/S38 addresses and the S18 cursor read into the selected
native word arithmetic. No inactive candidate pointer enters this certificate. -/
theorem PartyReads.of_rows {J : HistoryGatherBody.Layout} {m : Memory W} {node page kernel incident kind : ℕ}
    (cursor : J.nodePorts.cursor=base u 18) (nodes : J.nodePorts.nodes=base u 44)
    (cursorFit : base u 18<2^W) (nodeFit : base u 44+8*node+5<2^W)
    (current : (HistoryNodePorts.id J.nodePorts).value (fun _=>0) m (fun _=>0)=(node:Word W))
    (kern : (selected J m).kernel=(kernel:Word W)) (inc : (selected J m).incident=(incident:Word W))
    (cat : (selected J m).kindPage=(kind:Word W))
    (kerFit : kernel+4<2^W) (incFit : incident+5<2^W) (kindFit : kind+7≤2^W)
    (kerHigh : base u 18≤kernel) (incHigh : base u 18≤ incident) (kindHigh : base u 18≤kind)
    (pageHigh : base u 18≤page) : PartyReads u J m page := by
  have plus (a b : ℕ) (fit : a+b<2^W) :
      ((a:Word W)+(b:Word W)).val=a+b := by rw [←Nat.cast_add,Fin.val_cast_of_lt fit]
  have now : nodeWord J m=((base u 44+8*node:ℕ):Word W) := by
    change (J.nodePorts.nodes:Word W)+8*((HistoryNodePorts.id J.nodePorts).value (fun _=>0) m (fun _=>0))=_
    rw [nodes,current,Nat.cast_add,Nat.cast_mul];rfl
  refine ⟨by rw [cursor,Fin.val_cast_of_lt cursorFit],?_,?_,?_,?_,pageHigh⟩
  · have across:=apart (u:=u) (by decide : 18<44)
    rw [now,show (5:Word W)=((5:ℕ):Word W) by rfl,plus _ _ nodeFit]
    omega
  · intro j;rw [kern,plus _ _ (by have:=j.isLt;omega)];omega
  · intro j;rw [inc,plus _ _ (by have:=j.isLt;omega)];omega
  · intro j;rw [cat,plus _ _ (by have:=j.isLt;omega)];omega

/-- The gather decoder's arithmetic fits a native word from the per-bank field bounds. -/
theorem gather_scalar_room (age : 16≤u) (size bits e arity copies digit : ℕ)
    (g0 : size≤V) (g1 : bits≤V) (g2 : e≤V) (g3 : arity≤V) (g4 : copies≤V) (g5 : digit≤V) :
    2+size+bits+e+arity+e*bits+copies*(e*bits)+copies*arity+copies*digit<2^W := by
  have big:1024≤V:=Nat.pow_le_pow_right (by decide : 0<2)
    ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have a : e*bits≤V*V:=Nat.mul_le_mul g2 g1
  have b:=Nat.mul_le_mul g4 a
  have c:=Nat.mul_le_mul g4 g3
  have d:=Nat.mul_le_mul g4 g5
  have positive:0<V:=Nat.two_pow_pos _
  have v2:V≤V*V:=Nat.le_mul_of_pos_left V positive
  have v3:V*V≤V*(V*V):=Nat.le_mul_of_pos_left _ positive
  have many:=Nat.mul_le_mul_right (V*(V*V)) (show 12≤V by omega)
  have top:=word_space (i:=0) (u:=u) (by omega) (by change 0<V^4;positivity)
  change base u 0+V^4<2^W at top
  have volumePower : V*(V*(V*V))=V^4:=by ring
  omega

theorem gather_digit_room (age : 16≤u) (count copies : ℕ) (h : count≤V) (k : copies≤V) :
    count*copies≤2^W := by
  have :=gather_scalar_room (u:=u) age 0 0 0 count copies 0 (Nat.zero_le _) (Nat.zero_le _)
    (Nat.zero_le _) h k (Nat.zero_le _)
  simp only [Nat.mul_zero,Nat.add_zero] at this
  simpa [Nat.mul_comm] using (show copies*count≤2^W by omega)

theorem gather_source_room {p h : ℕ} (room : 2+p+h≤2^W) (b : BitSource h p) :
    sourceAddress b<2^W := by
  cases b with
  | hidden i => change 2+p+i.val<_;have:=i.isLt;omega
  | pin i => change 2+i.val<_;have:=i.isLt;omega
  | constant v =>
    cases v with
    | false => change 0<2^W; exact Nat.two_pow_pos _
    | true => change 1<2^W; omega

end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickWorkspace HistoryStageBody.Physical HistoryGatherBody HistoryGatherExecution
open private header_congr from OAI.ThreeFlat.RAM.HistoryGatherBody
open scoped Classical Fin.CommRing
noncomputable section
variable {u : ℕ}
local notation "W" => (16*u^10)
local notation "V" => volume u

variable {J : HistoryGatherBody.Layout} {m : Memory (16*u^10)} {node page size : ℕ}

/-- During a partial S17 write, header reproduction reads the same issued row and every
same catalog digit. An ignored or padded port contributes zero without a table read. -/
theorem PartySpace.header (A : PartySpace u J m node page size) (reads : PartyReads u J m page)
    {S : Diagonal.CompressorPacking.Native.Graph.Stage} (mode : J.mode=.shrink S)
    (pagePtr : (selected J m).portPage=(page:Word W))
    (extent : page+HistoryPortCatalogue.stride J.demandCap J.supplyCap J.digitCap≤2^W)
    (stage : ∀j:Fin 9,base u 18≤(m (selected J m).kernel.val+(j.val:Word W)).val)
    (widths : ∀side i,i<cap J side → portActive J m side i → base u 18≤ issuedCell J m side i) :
    HeaderFootprint J m J.temp (J.temp+(HistoryGatherBody.fields («W»:=W) J).length) := by
  constructor
  intro scratch frame
  have endHeader : J.temp+(HistoryGatherBody.fields («W»:=W) J).length≤portsEnd J := by
    rw [header_size];have:=A.hSize;unfold portsEnd;simp only [Nat.add_mul,Nat.one_mul];omega
  have read (a : ℕ) (high : base u 18≤a) : scratch a=m a := frame _ (.inr (endHeader.trans (A.stop.trans high)))
  have cursor:=read _ reads.cursor
  have nodeWord:=read _ reads.node
  have kernel : (selected J scratch).kernel=(selected J m).kernel := by
    change scratch (HistoryGatherBody.nodeWord J scratch+5).val=_
    rw [node_stable J cursor,nodeWord];rfl
  have rows:=selected_rows_same J cursor nodeWord (read _ (reads.kernel 4)) (read _ (reads.incident 2))
  have portRead (j : ℕ) (lt : j<HistoryPortCatalogue.stride J.demandCap J.supplyCap J.digitCap) :
      wordAt scratch (selected J scratch).portPage j=wordAt m (selected J m).portPage j := by
    rw [rows.2.2,pagePtr]
    unfold wordAt
    rw [←Nat.cast_add,Fin.val_cast_of_lt (show page+j<2^W by omega)]
    exact read _ (by have:=reads.page;omega)
  have mask : MaskRoom J m J.temp (J.temp+(HistoryGatherBody.fields («W»:=W) J).length) :=
    ⟨.inr (endHeader.trans (A.stop.trans reads.cursor)),.inr (endHeader.trans (A.stop.trans reads.node)),
      .inr (endHeader.trans (A.stop.trans (reads.kernel 3))),fun _=>.inr (endHeader.trans (A.stop.trans (reads.kernel 4))),
      fun _=>.inr (endHeader.trans (A.stop.trans (reads.incident 5)))⟩
  have active:=mask.active frame
  have port (side : Bool) (i : ℕ) : portActive J scratch side i ↔ portActive J m side i := by
    unfold portActive
    rw [propext active,portRead side.toNat (by
      cases side <;> simp [HistoryPortCatalogue.stride]; omega)]
  have atInc (j : Fin 6) : wordAt scratch (selected J scratch).incident j.val=wordAt m (selected J m).incident j.val := by
    unfold wordAt;rw [rows.1];exact read _ (reads.incident j)
  have stagePtr : scratch (selected J scratch).kernel.val=m (selected J m).kernel.val := by
    rw [kernel]
    exact read _ (by simpa using reads.kernel 0)
  have stageAt (j : Fin 9) :
      wordAt scratch (scratch (selected J scratch).kernel.val) j.val=wordAt m (m (selected J m).kernel.val) j.val := by
    unfold wordAt;rw [stagePtr];exact read _ (stage j)
  have code (side : Bool) (i : ℕ) (bound : i<cap J side) : portCode J scratch side i=portCode J m side i := by
    unfold portCode;apply portRead;cases side <;> dsimp [cap] at bound ⊢ <;>
      simp only [HistoryPortCatalogue.stride,HistoryPortCatalogue.supplyBase,HistoryPortCatalogue.demandBase] <;>omega
  have wide (side : Bool) (i : ℕ) (bound : i<cap J side) : physicalWidth J scratch side i=physicalWidth J m side i := by
    by_cases on : portActive J m side i
    · have cell : issuedCell J scratch side i=issuedCell J m side i := by
        have incidentOne : wordAt scratch (selected J scratch).incident 1 =
            wordAt m (selected J m).incident 1 := atInc 1
        have stageOne : wordAt scratch (scratch (selected J scratch).kernel.val) 1 =
            wordAt m (m (selected J m).kernel.val) 1 := stageAt 1
        have tab : wordAt scratch (scratch (selected J scratch).kernel.val) (if side then 3 else 8) =
            wordAt m (m (selected J m).kernel.val) (if side then 3 else 8) := by
          cases side
          · exact stageAt 8
          · exact stageAt 3
        simp only [issuedCell, incidentOne, stageOne, tab, code side i bound]
      simp only [physicalWidth,ite_eq_left ((port side i).mpr on),ite_eq_left on,mode]
      change scratch (issuedCell J scratch side i)=m (issuedCell J m side i)
      rw [cell];exact read _ (widths side i bound on)
    · have off : ¬ portActive J scratch side i := fun h => on ((port side i).mp h)
      simp only [physicalWidth, ite_eq_right off, ite_eq_right on]
  have count : partyMapCount J scratch=partyMapCount J m := by
    simp only [partyMapCount,propext active,wordAt,privatePage_stable J cursor 1]
    by_cases enabled:partyActive J m
    · simp only [ite_eq_left enabled];exact frame _ (.inl A.pairInfo)
    · simp only [ite_eq_right enabled]
  have payload (i : ℕ) (hi : i < J.supplyCap) : payloadWidth J scratch i = payloadWidth J m i := by
    have bits : wordAt scratch (selected J scratch).kindPage 2=wordAt m (selected J m).kindPage 2 := by
      unfold wordAt;rw [rows.2.1];exact read _ (reads.kind 2)
    have copies : wordAt scratch (selected J scratch).incident 3 =
        wordAt m (selected J m).incident 3 := atInc 3
    simp only [payloadWidth, propext active, copies, bits, wide true i hi]
  have tile (i : ℕ) (hi : i < J.demandCap) : tileWidth J scratch i = tileWidth J m i := by
    unfold tileWidth
    rw [propext (port false i)]
    split
    · apply portRead
      simp only [HistoryPortCatalogue.demandBase,HistoryPortCatalogue.stride];omega
    · rfl
  exact (header_congr J ((selected J scratch).privatePage 2) (partyMapCount J scratch)
    wide payload tile).trans (congrArg₂
      (numericHeaderWords J (physicalWidth J m) (payloadWidth J m) (tileWidth J m))
      (privatePage_stable J cursor 2) count)

end
end ThreeFlat.RAM.HistoryShrinkEmitter

end OAI
