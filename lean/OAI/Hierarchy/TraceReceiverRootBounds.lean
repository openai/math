import OAI.Hierarchy.TraceReceiverTerminalMap
import OAI.Hierarchy.TraceReceiverMapsRun
import OAI.ThreeFlat.RAM.TickTerminalRootGeometry
import OAI.ThreeFlat.RAM.HistoryNodeValueRetain
import OAI.ThreeFlat.RAM.HistoryNodeDirectoryFields
import OAI.ThreeFlat.Diagonal.HistoryPostorder

namespace OAI
/-! # Physical bounds for the receiver's selected S13 root -/

noncomputable section
namespace Hierarchy.TraceReceiverRootBounds

open ThreeFlat Diagonal PhysicalStage HistoryContraction
open RAM TickTerminalRoot HistoryTerminalTape HistoryStageBody.Physical HistoryStageSetup
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
open TickWorkspace

variable {W u d l p : ℕ} {F Pins : Type} [Field F] [Fintype F]

/-- The root dispatch reads the final-layer offset and the S17 ordinal
addressed by the live S18 counter. -/
theorem root_id {start «prefix» ordinal first selected : ℕ} (m : Memory W)
    (counter : natMemory m (base u 18)=ordinal) (pick : natMemory m (base u 17+ordinal)=selected)
    (initial : natMemory m (TickPhysicalABI.directory u 3)=first) :
    rootId (mounted u p start «prefix») (natMemory m)=first+selected := by
  change natMemory m (TickPhysicalABI.directory u 3)+natMemory m (base u 17+natMemory m (base u 18))=_
  rw [initial,counter,pick]

private theorem pin_span (X : State d l) (L : X.Words Pins) (z : X.Site) (T : Root)
    (raw : ℕ → ℕ) (suffix : ℕ) (rows : TraceReceiverTerminalMap.HalfRows X L z T raw suffix)
    (pins : T.localPins=L.ports.form.width z) : PinSpan T raw := by
  constructor
  · rw [rows.ext_eq,pins]
    exact Nat.le_add_right ..
  · intro j hj
    let i : Fin (L.count z) := ⟨j,by simpa only [rows.halves_eq] using hj⟩
    change T.ext+(half T raw i.val).start+(half T raw i.val).width≤T.localPins
    rw [rows.ext_eq,rows.start i,rows.width i,pins,Nat.add_assoc]
    exact Nat.add_le_add_left (Tree.prefix_next_le (L.ports.lengths z) i) _

/-- The complete S9 gather fits even when the selected list is empty.
Each selected four-word record stream and the count fit one volume. -/
theorem total_room {n : ℕ} (rows : Fin n → ℕ) (large : 1≤volume u)
    (count : n≤volume u) (records : ∀ j,4*rows j≤volume u) :
    4*(∑ j,rows j)≤ stride u := by
  have each := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => records j)
  rw [←Finset.mul_sum] at each
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at each
  have twice:=Nat.mul_le_mul_right (volume u) count
  have top : volume u ^ 2 ≤ volume u ^ 4 := Nat.pow_le_pow_right large (by decide)
  change _≤volume u^4
  nlinarith only [each,twice,top]

/-- The current root's complete four-word stream ends inside the same S9
allocation as every previously selected ordinal. -/
theorem prefix_room {n : ℕ} (rows : Fin n → ℕ) (i : Fin n) (large : 1≤volume u)
    (count : n≤volume u) (records : ∀ j,4*rows j≤volume u) :
    4*(Tree.before rows i+rows i)≤ stride u :=
  (Nat.mul_le_mul_left 4 (Tree.prefix_next_le rows i)).trans (total_room rows large count records)

omit [Field F] [Fintype F] in
/-- The selected S17 word chooses the S44 archive row and the synchronous
S13 result. The final incident header and its four-word records come from the
actual archive, and the edge prefix comes from the executed wire scan. -/
theorem selected {n suffix seedCount heapLo heapHi : ℕ}
    (m mid : Memory W) (X : State d l) (L : X.Words Pins) (O : X.ArchiveSites) (z : X.Site)
    (order : X.OrderedHalves L) (value : NodeValue F) (tag : ((Fin 3 → Bool) → F) → ℕ)
    (b : NavigationNodeRows.Banks) (x : TerminalWireArchive.Layout)
    (i : Fin n) (rows : Fin n → ℕ)
    (cap : base u 45 < 2^W) (large : 162≤volume u) (nodeLimit : O.layer.first+O.layer.count≤volume u)
    (count : n≤volume u) (perRow : ∀ j,4*rows j≤volume u)
    (degree : 2*d≤volume u) (pinLimit : value.pins≤volume u)
    (word : 2+p<2^W) (suffixIn : suffix≤p)
    (area : base u 18+stride u≤heapLo) (heapFit : heapHi≤2^W)
    (wireAbove : base u 18+stride u≤x.prefixBase) (wireFit : TerminalWireArchive.Bounds x W)
    (edgeCount : x.edges=X.edgeCount) (widths : ∀ j : Fin X.edgeCount,(mid (x.widthBase+j.val)).val=X.wireWidth j)
    (wireCapacity : X.widthSum≤x.capacity)
    (prefixKept : ∀ j : Fin X.edgeCount,
      m (x.prefixBase+j.val)=TerminalWireArchive.image x mid (x.prefixBase+j.val))
    (counter : natMemory m (base u 18)=i.val)
    (pick : natMemory m (base u 17+i.val)=(O.ord z).val)
    (initial : natMemory m (TickPhysicalABI.directory u 3)=O.layer.first)
    (nodePointer : natMemory m (TickPhysicalABI.directory u 3+1)=b.nodes)
    (tableAt : b.nodes=base u 44)
    (directory : DirectoryRow b O.layer (O.ord z) m)
    (posted : X.HalfRows O (fun a=>heapLo≤a ∧ a<heapHi) (natMemory m))
    (cache : value.Cached tag u (O.id z) m)
    (external : value.external=L.ext z) (localPins : value.pins=L.ports.form.width z)
    (streamAt' : value.stream=streamAt u seedCount (O.id z))
    (endsAt' : value.ext=endsAt u seedCount (O.id z))
    (prefixRows : natMemory m (base u 18+2)=Tree.before rows i) (rowCount : rows i=value.net.cells) :
    let A:=mounted u p (2+suffix) x.prefixBase
    RootBounds A m ∧ TraceReceiverTerminalMap.HalfRows X L z (terminal A (natMemory m)) (natMemory m) suffix ∧
      CompactRootAt u p (2+suffix) x.prefixBase m := by
  let A:=mounted u p (2+suffix) x.prefixBase
  let raw:=natMemory m
  let T:=terminal A raw
  let idx:=O.id z
  let hd:=O.layer.incident+(O.ord z).val*2
  have nodeBase : raw (TickPhysicalABI.directory u 3+1)=b.nodes:=nodePointer
  have prefixCount : raw (base u 18+2)=Tree.before rows i:=prefixRows
  have index : rootId A raw=idx := root_id m counter pick initial
  have room := TickWorkspace.apart (u:=u) (by decide : 18<45)
  have rootHeader:=posted.headerSafe z (0 : Fin 2)
  change heapLo≤hd+0 ∧ hd+0<heapHi at rootHeader
  have ptr : raw (raw (A.rootHeader+1)+8*rootId A raw+6)=hd := by
    change raw (raw (TickPhysicalABI.directory u 3+1)+8*rootId A raw+6)=hd
    rw [nodeBase,index]
    exact (congrArg Fin.val directory.incident).trans (Fin.val_cast_of_lt (by omega : hd<2^W))
  have halfCount : T.halves=raw hd := by change raw _=_; rw [ptr]
  have dataAddr : T.halfData=raw (hd+1) := by change raw (_+1)=_; rw [ptr]
  have header : HistoryStageRoot.atResult raw (A.results+8*rootId A raw)=value.info := by
    rw [index]
    exact cache.header
  have ext : T.ext=value.external := congrArg HistoryStageRoot.Result.extCount header
  have pins : T.localPins=value.pins := congrArg HistoryStageRoot.Result.pins header
  have ends : T.endpoints=value.ext := congrArg HistoryStageRoot.Result.ext header
  have cells : T.rows=value.net.cells := congrArg HistoryStageRoot.Result.rows header
  have stream : T.stream=value.stream := congrArg HistoryStageRoot.Result.stream header
  have halfRows : TraceReceiverTerminalMap.HalfRows X L z T raw suffix :=
    TraceReceiverTerminalMap.of_emitted X L z T raw suffix O posted order (ext.trans external) rfl
      halfCount dataAddr (fun e => (congrArg Fin.val (prefixKept (X.wireOrder e))).trans
        (TraceReceiverTerminalMap.prefix_image X x mid wireFit edgeCount widths wireCapacity e))
  have nc : idx<volume u := by
    have := (O.ord z).isLt
    dsimp [idx,State.ArchiveSites.id]
    omega
  let V:=volume u
  have square : V^2≤V^4 := Nat.pow_le_pow_right (by omega : 1≤V) (by decide)
  have cube : V^3≤V^4 := Nat.pow_le_pow_right (by omega : 1≤V) (by decide)
  have enough : 8*V+16≤ stride u := by
    change _≤V^4
    have h := Nat.mul_le_mul_right V (show 162≤V from large)
    nlinarith only [h,square,large]
  have little : 65≤ stride u := by omega
  have oldSpace := (perRow i)
  rw [rowCount] at oldSpace
  have extSpace : value.external≤V := by
    have e : L.ext z≤L.ports.form.width z := Nat.le_add_right ..
    rw [←external,←localPins] at e
    exact e.trans pinLimit
  obtain ⟨low,between,last⟩ := address_limits (u:=u) (seedCount:=seedCount) (i:=idx) large oldSpace extSpace
  have slot:=Nat.mul_le_mul_right (V^2) (show idx+1≤V by omega)
  have within : (idx+1)*V^2≤ stride u := by change _ ≤ V^4; nlinarith only [slot,cube]
  have recordRoom : (idx+1)*(volume u)^2 ≤ stride u := within
  have from12:=apart (u:=u) (by decide : 12<14)
  have from10:=apart (u:=u) (by decide : 10<12)
  rw [←streamAt'] at low between
  rw [←endsAt'] at between last
  have pEnd:=wireFit.prefix
  have nEnd:=apart (u:=u) (by decide : 44<45)
  have nStart:=apart (u:=u) (by decide : 18<44)
  have number:=halfCount.trans (posted.count z)
  have budget:=prefix_room rows i (by omega : 1≤volume u) count perRow
  suffices compact : CompactRootAt u p (2+suffix) x.prefixBase m from
    ⟨CompactRootAt.bounds (room.trans_lt cap) compact,halfRows,compact⟩
  refine ⟨little,⟨by omega,by omega,by omega⟩,?_,?_,?_,?_,?_,?_,?_,?_,
    pin_span X L z T raw suffix halfRows (pins.trans localPins),?_,?_,?_⟩
  · rw [counter]
    have := i.isLt
    omega
  · change base u 13+8*rootId A raw+6≤base u 14
    rw [index]
    have := apart (u:=u) (by decide : 13<14)
    omega
  · change ImmutableBankAt W u (raw (TickPhysicalABI.directory u 3+1)+8*rootId A raw+6) 1
    rw [nodeBase,tableAt,index]
    exact ⟨Or.inr (by omega),by omega⟩
  · change ImmutableBankAt W u (raw (raw (A.rootHeader+1)+8*rootId A raw+6)) 2
    rw [ptr]
    have hi := posted.headerSafe z (1 : Fin 2)
    change heapLo≤hd+1 ∧ hd+1<heapHi at hi
    exact ⟨Or.inr (by omega),by omega⟩
  · change ∀ j<4*T.halves,ImmutableBankAt W u (T.halfData+j) 1
    intro j hj
    rw [number] at hj
    let row : Fin (2*d) := ⟨j/4,by omega⟩
    let col : Fin 4 := ⟨j%4,by omega⟩
    have pos := posted.entriesSafe z row col
    change heapLo≤raw (hd+1)+4*(j/4)+j%4 ∧ raw (hd+1)+4*(j/4)+j%4<heapHi at pos
    rw [dataAddr]
    exact ⟨Or.inr (by omega),by omega⟩
  · change ∀ j<T.halves,ImmutableBankAt W u (x.prefixBase+(half T raw j).edge) 1
    intro j hj
    let e : Fin (L.count z) := ⟨j,by simpa only [halfRows.halves_eq] using hj⟩
    rw [show (half T raw j).edge=_ from halfRows.edge e]
    have hr := (X.wireOrder (L.order z e).1.1).isLt
    exact ⟨Or.inr (by omega),by omega⟩
  · change 7*(T.halves+2)≤_
    rw [number]; omega
  · change 64+T.localPins≤_
    rw [pins]; omega
  · change T.endpoints+T.ext≤_
    rw [ends,ext]; omega
  · change base u 9+4*raw (base u 18+2)+4*T.rows≤_
    rw [prefixCount,cells,←rowCount];omega
  · change base u 10≤T.stream ∧ T.stream+4*T.rows≤base u 14
    rw [stream,cells];constructor <;> omega

section Frame
variable {wireStart wirePrefix : ℕ} {m : Memory W}
set_option quotPrecheck false
local notation "A" => mounted u p wireStart wirePrefix
local notation "T" => terminal A (natMemory m)

private theorem kept (compact : CompactRootAt u p wireStart wirePrefix m)
    (cap : base u 18+stride u<2^W) (a : ℕ)
    (slabs : a<base u 14 ∨ base u 17≤a)
    (state : a<base u 18 ∨ base u 18+4≤a) (row : a<(T).meta ∨ (T).meta+4*(T).rows≤a) :
    TraceReceiverTasks.KeptByRoot A m a := by
  have space:=compact.space
  have seed:=apart (u:=u) (by decide : 14<15)
  have command:=apart (u:=u) (by decide : 15<16)
  have argument:=apart (u:=u) (by decide : 16<17)
  have finish:=apart (u:=u) (by decide : 17<18)
  have table : 7*((T).halves+2)≤ stride u := compact.tableWords
  have pins : 64+(T).localPins≤ stride u := compact.mapWords
  have safe : (((base u 14+5:ℕ):Word W)).val=base u 14+5 := Fin.val_cast_of_lt (by omega)
  refine ⟨⟨?_,jobs_span T (natMemory m) (((A).seed+5:ℕ):Word W) (readyImage A m)
    compact.span a ?_ row⟩,state,?_,?_,?_⟩
  · change a≠((base u 14+5:ℕ):Word W).val
    rw [safe]
    omega
  · change a<base u 14+64 ∨ base u 14+64+(T).localPins≤a
    omega
  · change a<base u 14 ∨ base u 14+26≤a
    omega
  · change a<base u 15 ∨ base u 15+7*((T).halves+2)≤a
    omega
  · change a<base u 16 ∨ base u 16+7*((T).halves+2)≤a
    omega

/-- S18+4 and all higher words, including the S44 directory, the archived
incident rows and every sector-30 task, command and saved-map word. -/
theorem kept_high (compact : CompactRootAt u p wireStart wirePrefix m)
    (cap : base u 18+stride u<2^W) (a : ℕ) (high : base u 18+4≤a) :
    TraceReceiverTasks.KeptByRoot A m a := by
  have loc:=apart (u:=u) (by decide : 17<18)
  have data:=apart (u:=u) (by decide : 9<18)
  have endRows : (T).meta+4*(T).rows≤base u 9+stride u := compact.metadata
  exact kept compact cap a (Or.inr (by omega)) (Or.inr high) (Or.inr (by omega))

/-- The final-layer S11 descriptor, S12 source and endpoint arrays, S13
results and the S17 selected list survive each root interpreter. -/
theorem kept_archive (compact : CompactRootAt u p wireStart wirePrefix m)
    (cap : base u 18+stride u<2^W) (a : ℕ)
    (region : (base u 10≤a ∧ a<base u 14) ∨ (base u 17≤a ∧ a<base u 18)) :
    TraceReceiverTasks.KeptByRoot A m a := by
  have b9:=apart (u:=u) (by decide : 9<10)
  have b10:=apart (u:=u) (by decide : 10<17)
  have b14:=apart (u:=u) (by decide : 14<18)
  have endRows : (T).meta+4*(T).rows≤base u 9+stride u := compact.metadata
  exact kept compact cap a (by omega) (by omega) (Or.inr (by omega))

/-- The S18+4 countdown word is outside all writes to S18+0 through +3. -/
theorem counter (compact : CompactRootAt u p wireStart wirePrefix m)
    (cap : base u 18+stride u<2^W) :
    TraceReceiverTasks.KeptByRoot A m (countdown (W:=W) A).val := by
  have wide:=compact.space
  have addr : (countdown (W:=W) A).val=base u 18+4 := Fin.val_cast_of_lt (show base u 18+4<2^W by omega)
  rw [addr]
  exact kept_high compact cap _ le_rfl

/-- The selected-root interpreter increments its true ordinal, row prefix
and private-bit prefix and retains the original count in the S18 header. -/
theorem controls (compact : CompactRootAt u p wireStart wirePrefix m)
    (cap : base u 18+stride u<2^W) (j : Fin 4) :
    output A m ((A).control+j.val)=(seedWords A (natMemory m) (Fin.natAdd 22 j):Word W) := by
  have b9:=apart (u:=u) (by decide : 9<14)
  have b14:=apart (u:=u) (by decide : 14<18)
  have space:=compact.space
  have metaEnd : (T).meta+4*(T).rows≤base u 9+stride u := compact.metadata
  refine counts_out A m (CompactRootAt.bounds cap compact) ?_ j
  intro k
  have hk:=k.isLt
  have cur : (((A).seed+5:ℕ):Word W).val=base u 14+5 := Fin.val_cast_of_lt (by change base u 14+5<2^W;omega)
  refine ⟨?_,jobs_span T (natMemory m) (((A).seed+5:ℕ):Word W) (readyImage A m)
    compact.span _ (Or.inl ?_) (Or.inr ?_)⟩
  · rw [cur]
    change base u 14+22+k.val≠base u 14+5
    omega
  · change base u 14+22+k.val<base u 14+64
    omega
  · change (T).meta+4*(T).rows≤base u 14+22+k.val
    omega

/-- The sector-30 map copy following a root leaves all four just-written
control words in place. -/
theorem map_controls (tasks hdr dst len : ℕ) (initial : Memory W)
    (compact : CompactRootAt u p wireStart wirePrefix (TraceReceiverTasks.mapSeed A tasks hdr initial))
    (cap : base u 18+stride u<2^W) (above : base u 18+4≤dst) (j : Fin 4) :
    TraceReceiverTasks.mapStep A tasks hdr dst len initial ((A).control+j.val)=
      (seedWords A (natMemory (TraceReceiverTasks.mapSeed A tasks hdr initial)) (Fin.natAdd 22 j):Word W) := by
  have hj:=j.isLt
  have outside : ¬(dst≤(A).control+j.val ∧ (A).control+j.val<dst+len) := by
    change ¬(dst≤base u 18+j.val ∧ base u 18+j.val<dst+len)
    omega
  simpa only [TraceReceiverTasks.mapStep,RAM.fillSegment,ite_eq_right outside] using controls compact cap j

/-- Earlier S9 output is preserved as the root extends its prefix. -/
theorem kept_before (compact : CompactRootAt u p wireStart wirePrefix m)
    (cap : base u 18+stride u<2^W) (a : ℕ) (before : a<(T).meta) :
    TraceReceiverTasks.KeptByRoot A m a := by
  have b9:=apart (u:=u) (by decide : 9<14)
  have b14:=apart (u:=u) (by decide : 14<18)
  have endRows : (T).meta+4*(T).rows≤base u 9+stride u := compact.metadata
  exact kept compact cap a (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl before)

/-- The native pin saved from S14 is outside the seed cursor, S9 output
and the four S18 control writes. -/
theorem map_pin_room (compact : CompactRootAt u p wireStart wirePrefix m)
    (cap : base u 18+stride u<2^W) (k : Fin (T).localPins) :
    (A).map+k.val≠(((A).seed+5:ℕ):Word W).val ∧
      ((A).map+k.val<(T).meta ∨ (T).meta+4*(T).rows≤(A).map+k.val) ∧
      ((A).map+k.val<(A).control ∨ (A).control+4≤(A).map+k.val) := by
  have b9:=apart (u:=u) (by decide : 9<14)
  have b14:=apart (u:=u) (by decide : 14<18)
  have space:=compact.space
  have pins : 64+(T).localPins≤ stride u := compact.mapWords
  have metaEnd : (T).meta+4*(T).rows≤base u 9+stride u := compact.metadata
  have offset:=k.isLt
  have cur : (((A).seed+5:ℕ):Word W).val=base u 14+5 := Fin.val_cast_of_lt (by change base u 14+5<2^W;omega)
  rw [cur]
  change base u 14+64+k.val≠base u 14+5 ∧
    (base u 14+64+k.val<(T).meta ∨ (T).meta+4*(T).rows≤base u 14+64+k.val) ∧
    (base u 14+64+k.val<base u 18 ∨ base u 18+4≤base u 14+64+k.val)
  exact ⟨by omega,Or.inr (by omega),Or.inl (by omega)⟩

omit [Field F] [Fintype F] in
/-- A saved sector-30 word reads its true terminal wire or external input.
External addresses come from the cached S12 endpoints of this same S13 node. -/
theorem cached_saved_pin (compact : CompactRootAt u p wireStart wirePrefix m)
    (cap : base u 18+stride u<2^W) (X : State d l) (L : X.Words Pins) (z : X.Site)
    (ext : ∀ z,Fin (L.ext z)→Fin p) (suffix dst idx : ℕ) (room : suffix+X.widthSum≤p)
    (rows : TraceReceiverTerminalMap.HalfRows X L z T (natMemory m) suffix)
    (value : NodeValue F) (tag : ((Fin 3→Bool)→F)→ℕ)
    (selected : rootId A (natMemory m)=idx) (cache : value.Cached tag u idx m)
    (pins : value.pins=L.ports.form.width z) (external : value.external=L.ext z)
    (origin : ∀ j : Fin (L.ext z),value.endpoint (j.cast external.symm)=2+(ext z j).val)
    (k : Fin (L.ports.form.width z)) :
    fillSegment dst (L.ports.form.width z) (fun a=>output A m ((A).map+(a-dst))) (output A m) (dst+k.val)
      =((2+(L.ports.physicalSource ext (TraceReceiverTerminalMap.shared X suffix room) z k).val:ℕ):Word W) := by
  have header : HistoryStageRoot.atResult (natMemory m) ((A).results+8*rootId A (natMemory m))=value.info := by
    rw [selected]
    exact cache.header
  have portCount : (T).localPins=L.ports.form.width z := (congrArg HistoryStageRoot.Result.pins header).trans pins
  have ep : (T).endpoints=value.ext := congrArg HistoryStageRoot.Result.ext header
  have reaches (j : Fin (L.ext z)) : m ((T).endpoints+j.val)=((2+(ext z j).val:ℕ):Word W) := by
    rw [ep,←origin j]
    exact cache.ends (j.cast external.symm)
  have fit:=map_pin_room compact cap (k.cast portCount.symm)
  exact TraceReceiverTerminalMap.saved_pin X L z ext suffix room A m dst (CompactRootAt.bounds cap compact)
    rows reaches compact.endpoints k fit.1 fit.2.1 fit.2.2

end Frame

end Hierarchy.TraceReceiverRootBounds

end
end OAI
