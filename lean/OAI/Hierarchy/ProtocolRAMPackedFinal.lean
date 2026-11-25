import OAI.Hierarchy.ProtocolRAMFrozenAnchors
import OAI.Hierarchy.ProtocolRAMPackedRanked
import OAI.Hierarchy.TaggedShorterSlotWidthPublish

namespace OAI
/-! # One format of the physical board, recomputed after supergroup remapping -/

namespace Hierarchy.ProtocolRAMPackedFinal

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat Routing CallPool RAM RAM.DescriptorExpr PhysicalProcedure
open ProtocolRAM TaggedShorterEmitMachine TaggedShorterReportedPublish
open TaggedShorterGroups TaggedShorterReportAdvice
open ProtocolRAMFrozenWidthFrame
open ProtocolRAMTranslatedKey ProtocolRAMReportedPorts
open scoped Classical Fin.CommRing

variable {W N gb : ℕ}

theorem publish_stored {groups D B M n w menu cap rom bits base src sink γ : ℕ}
    (L : ProtocolRAMPackedRanked.Layout) (width packed bias classes weights left right : Bank)
    (rows : Fin N→ProtocolRAMEmit.Row) (lr : Bool→Fin N→ℕ) (mem : Memory W)
    (fit : L.Fits W N (2^gb*(menu+1)))
    (wf : width.Fits W L.spread) (gf : packed.Fits W L.spread) (bf : bias.Fits W L.spread)
    (cf : classes.Fits W L.spread) (xf : weights.Fits W L.spread) (lf : left.Fits W L.spread)
    (rf : right.Fits W L.spread)
    (wRead : ∀i : Fin N,width.read mem ((3*i.val:ℕ):Word W)=((rows i).width:Word W))
    (gRead : ∀i : Fin N,packed.read mem (i.val:Word W)=((rows i).group:Word W))
    (directory : ∀a : Word W,bias.read mem a=(((a.val%(2^gb))*(menu+1):ℕ):Word W))
    (classData : ∀i : Fin N,classes.read mem ((rows i).width:Word W)=((classOf rows w menu i).val:Word W))
    (copies : ∀i : Fin N,weights.read mem ((rows i).width:Word W)=(pieces rows w i:Word W))
    (leftRead : ∀i : Fin N,left.read mem (i.val:Word W)=(lr false i:Word W))
    (rightRead : ∀i : Fin N,right.read mem (i.val:Word W)=(lr true i:Word W))
    (groupCount : groups≤2^gb) (wideG : 2^gb≤2^W) (chronological : StrictMono (fun i=>(rows i).link))
    (protectedROM : ∀j : Fin 13,(bank rom bits j).Fits W L.spread)
    (read : ∀ j : Fin 13,∀ x : ℕ,x<2^bits → (bank rom bits j).read mem (x:Word W)=
      words groups D B M base w menu cap j x)
    (gFit : ∀i,0 < ProtocolRAMReportedPorts.pieces rows w i → (rows i).group < groups) (distinct : Function.Injective fun i=>(rows i).link)
    (bound : ∀g : Fin groups,size rows w menu γ g ≤ D)
    (copied : ∀i,ProtocolRAMReportedPorts.pieces rows w i ≤ cap)
    (pl : ∀g : Fin groups,Bool → Fin (size rows w menu γ g) ↪ Fin D)
    (located : ∀ b (g : Fin groups) (u : ProtocolRAMReportedPorts.Unit rows w menu γ g.val),
      (pl g b (ProtocolRAMReportedPorts.common rows w menu γ g.val distinct u)).val=
        lr b u.1.val+u.2.val)
    (groupCap : groups≤2^bits) (boundCap : D≤2^bits) (mapCap : groups*poolBatchCount D B≤2^bits)
    (tableCap : 10*(N*cap)≤2^bits) (widthFit : ∀i,(rows i).width<2^bits) (wide : 2^bits≤2^W)
    (menuFits : menu<2^W) (typeFits : γ ≤ menu) (small : 10≤2^W) (slotFits : cap<2^W)
    (hb : 0 < B) (hw : B≤2^n) (batchFits : B≤2^W)
    (layoutFit : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D))≤2^W)
    (ordered : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D)) ≤ src)
    (room : src+10*(N*cap)<2^W) (sinkLow : sink < src)
    (apart : ∀ f, (sink:Word W)≠TaggedShorterScatter.layout (capacity (Fin groups) D B M) D base layoutFit f)
    (input : (term (tables rom bits width L.group L.rank left right) γ sink).Fits W src)
    (low : (term (tables rom bits width L.group L.rank left right) γ sink).Fits W base)
    (payloadBase payloadSrc payloadSink : ℕ) (origins : Bank)
    (protectedOrigins : origins.Fits W L.spread)
    (og : ∀ g : Fin groups,origins.read mem (g.val:Word W)=((payloadBase+2*g.val*D:ℕ):Word W))
    (saveW : Safe width base sink) (saveG : Safe L.group base sink) (saveC : Safe L.rank base sink)
    (saveL : Safe left base sink) (saveR : Safe right base sink)
    (saveO : Safe origins base sink) (saveROM : ∀ j : Fin 13,Safe (bank rom bits j) base sink)
    (following : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D)) ≤ payloadBase)
    (payOrder : payloadBase+2*groups*D ≤ payloadSrc) (payRoom : payloadSrc+10*(N*cap)<2^W)
    (paySink : payloadSink < base) (payApart : ∀x : TaggedShorterSlotWidth.Slot groups D,
      payloadSink≠TaggedShorterSlotWidth.index payloadBase x)
    (payFit : (TaggedShorterSlotWidth.term
      (tables rom bits width L.group L.rank left right) origins D γ payloadSink).Fits W payloadSrc)
    (payLow : (TaggedShorterSlotWidth.term
      (tables rom bits width L.group L.rank left right) origins D γ payloadSink).Fits W payloadBase) :
    let A := tables rom bits width L.group L.rank left right
    let C := capacity (Fin groups) D B M
    let total := C+2*(C*2*D)
    let c := size (groups:=groups) rows w menu γ
    let addr := TaggedShorterScatter.layout C D base layoutFit
    let writeWidths := TaggedShorterSlotWidth.procedure W payloadBase groups D payloadSrc (N*cap) γ payloadSink A origins
    let prep := ProtocolRAMPackedRanked.program L W N (2^gb*(menu+1)) width packed bias classes weights
    let paid := ProtocolRAMPackedRanked.clock L N (2^gb*(menu+1)) width packed bias classes weights
    ∃ out,(prep.seq ((clearedProcedure W base total src (N*cap) γ sink A).seq writeWidths)).Exec mem out
      (paid+(((4+6*total)+(8+16230*(N*cap)))+((4+6*(2*groups*D))+(8+4130*(N*cap))))) ∧
      (∀ x : TaggedShorterSlotWidth.Slot groups D,out (TaggedShorterSlotWidth.index payloadBase x)=
        (TaggedShorterSlotWidth.value pl (TaggedShorterSlotWidth.reportWidth rows w menu γ distinct) x:Word W)) ∧
      (∀ i,decide ((out (addr (.inl i)).val).val≠0)=groupOccupied c bound B M i) ∧
      (∀ sb x,decide ((out (addr (.inr (false,sb,x))).val).val≠0)=groupMask c bound B M pl sb x) ∧
      (∀ sb x,Computability.VPVNP.RAMSerialization.wordBits n (((out (addr (.inr (true,sb,x))).val).val:ℕ):Word n)=
        groupID c bound M hb hw pl sb x) ∧
      (∀ f : TaggedShorterScatter.Field C D,out (addr f).val=(TaggedShorterScatter.contents c bound hb hw pl f:Word W)) ∧
      (∀ a,a < L.spread→a < base→a≠sink→a≠payloadSink→ out a=mem a) := by
  intro A C total c addr writeWidths prep paid
  let cr (i : Fin N) := TaggedShorterCommonScan.earlier (rowKey W gb w menu rows) (pieces rows w) i.val
    (rowKey W gb w menu rows i)
  obtain ⟨mid,runPrep,dyn,keep⟩ := ProtocolRAMPackedRanked.run L width packed bias classes weights left right rows
    lr mem fit wf gf bf cf xf lf rf wRead gRead directory classData copies leftRead rightRead
  have before (k : Bank) (kf : k.Fits W L.spread) (v : Word W) : k.read mid v=k.read mem v := by
    apply keep
    exact (Nat.add_lt_add_left (Nat.mod_lt v.val kf.1) _).trans_le kf.2.2
  have romIn (j : Fin 13) (x : ℕ) (hx : x<2^bits) :
      (bank rom bits j).read mid (x:Word W)=words groups D B M base w menu cap j x :=
    (before _ (protectedROM j) _).trans (read j x hx)
  have originsIn (g : Fin groups) : origins.read mid (g.val:Word W)=((payloadBase+2*g.val*D:ℕ):Word W) :=
    (before _ protectedOrigins _).trans (og g)
  have equalRank (g : Fin groups) (i : InGroup rows w menu γ g.val) : cr i.val=
      ProtocolRAMPortRanks.«prefix» (slotCount rows w menu γ g.val) (fun j=>(rows j.val).link) i :=
    ProtocolRAMTranslatedKey.rank_eq rows wideG groupCount gFit chronological g i
  obtain ⟨out,board,raw,occup,mask,ids,stored,frame⟩ := ProtocolRAMFrozenFinal.publish_from_anchors_stored mid rows
    width L.group L.rank left right cr lr dyn romIn gFit distinct bound copied equalRank pl located groupCap
    boundCap mapCap tableCap widthFit wide menuFits typeFits small slotFits hb hw batchFits layoutFit
    ordered room sinkLow apart input low payloadBase payloadSrc payloadSink origins originsIn saveW saveG
    saveC saveL saveR saveO saveROM following payOrder payRoom paySink payApart payFit payLow
  refine ⟨out,?_,raw,occup,mask,ids,stored,fun a h lo ns np=>(frame a lo ns np).trans (keep a h)⟩
  intro P R K mach pc reg pub exit install vals cfg rawMem entry eq
  exact Procedure.Exec.then runPrep board mach pc reg pub exit install vals cfg rawMem entry eq

theorem publish {groups D B M n w menu cap rom bits base src sink γ : ℕ}
    (L : ProtocolRAMPackedRanked.Layout) (width packed bias classes weights left right : Bank)
    (rows : Fin N→ProtocolRAMEmit.Row) (lr : Bool→Fin N→ℕ) (mem : Memory W)
    (fit : L.Fits W N (2^gb*(menu+1)))
    (wf : width.Fits W L.spread) (gf : packed.Fits W L.spread) (bf : bias.Fits W L.spread)
    (cf : classes.Fits W L.spread) (xf : weights.Fits W L.spread) (lf : left.Fits W L.spread)
    (rf : right.Fits W L.spread)
    (wRead : ∀i : Fin N,width.read mem ((3*i.val:ℕ):Word W)=((rows i).width:Word W))
    (gRead : ∀i : Fin N,packed.read mem (i.val:Word W)=((rows i).group:Word W))
    (directory : ∀a : Word W,bias.read mem a=(((a.val%(2^gb))*(menu+1):ℕ):Word W))
    (classData : ∀i : Fin N,classes.read mem ((rows i).width:Word W)=((classOf rows w menu i).val:Word W))
    (copies : ∀i : Fin N,weights.read mem ((rows i).width:Word W)=(pieces rows w i:Word W))
    (leftRead : ∀i : Fin N,left.read mem (i.val:Word W)=(lr false i:Word W))
    (rightRead : ∀i : Fin N,right.read mem (i.val:Word W)=(lr true i:Word W))
    (groupCount : groups≤2^gb) (wideG : 2^gb≤2^W) (chronological : StrictMono (fun i=>(rows i).link))
    (protectedROM : ∀j : Fin 13,(bank rom bits j).Fits W L.spread)
    (read : ∀ j : Fin 13,∀ x : ℕ,x<2^bits → (bank rom bits j).read mem (x:Word W)=
      words groups D B M base w menu cap j x)
    (gFit : ∀i,0 < ProtocolRAMReportedPorts.pieces rows w i → (rows i).group < groups) (distinct : Function.Injective fun i=>(rows i).link)
    (bound : ∀g : Fin groups,size rows w menu γ g ≤ D)
    (copied : ∀i,ProtocolRAMReportedPorts.pieces rows w i ≤ cap)
    (pl : ∀g : Fin groups,Bool → Fin (size rows w menu γ g) ↪ Fin D)
    (located : ∀ b (g : Fin groups) (u : ProtocolRAMReportedPorts.Unit rows w menu γ g.val),
      (pl g b (ProtocolRAMReportedPorts.common rows w menu γ g.val distinct u)).val=
        lr b u.1.val+u.2.val)
    (groupCap : groups≤2^bits) (boundCap : D≤2^bits) (mapCap : groups*poolBatchCount D B≤2^bits)
    (tableCap : 10*(N*cap)≤2^bits) (widthFit : ∀i,(rows i).width<2^bits) (wide : 2^bits≤2^W)
    (menuFits : menu<2^W) (typeFits : γ ≤ menu) (small : 10≤2^W) (slotFits : cap<2^W)
    (hb : 0 < B) (hw : B≤2^n) (batchFits : B≤2^W)
    (layoutFit : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D))≤2^W)
    (ordered : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D)) ≤ src)
    (room : src+10*(N*cap)<2^W) (sinkLow : sink < src)
    (apart : ∀ f, (sink:Word W)≠TaggedShorterScatter.layout (capacity (Fin groups) D B M) D base layoutFit f)
    (input : (term (tables rom bits width L.group L.rank left right) γ sink).Fits W src)
    (low : (term (tables rom bits width L.group L.rank left right) γ sink).Fits W base)
    (payloadBase payloadSrc payloadSink : ℕ) (origins : Bank)
    (protectedOrigins : origins.Fits W L.spread)
    (og : ∀ g : Fin groups,origins.read mem (g.val:Word W)=((payloadBase+2*g.val*D:ℕ):Word W))
    (saveW : Safe width base sink) (saveG : Safe L.group base sink) (saveC : Safe L.rank base sink)
    (saveL : Safe left base sink) (saveR : Safe right base sink)
    (saveO : Safe origins base sink) (saveROM : ∀ j : Fin 13,Safe (bank rom bits j) base sink)
    (following : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D)) ≤ payloadBase)
    (payOrder : payloadBase+2*groups*D ≤ payloadSrc) (payRoom : payloadSrc+10*(N*cap)<2^W)
    (paySink : payloadSink < base) (payApart : ∀x : TaggedShorterSlotWidth.Slot groups D,
      payloadSink≠TaggedShorterSlotWidth.index payloadBase x)
    (payFit : (TaggedShorterSlotWidth.term
      (tables rom bits width L.group L.rank left right) origins D γ payloadSink).Fits W payloadSrc)
    (payLow : (TaggedShorterSlotWidth.term
      (tables rom bits width L.group L.rank left right) origins D γ payloadSink).Fits W payloadBase) :
    let A := tables rom bits width L.group L.rank left right
    let C := capacity (Fin groups) D B M
    let total := C+2*(C*2*D)
    let c := size (groups:=groups) rows w menu γ
    let addr := TaggedShorterScatter.layout C D base layoutFit
    let writeWidths := TaggedShorterSlotWidth.procedure W payloadBase groups D payloadSrc (N*cap) γ payloadSink A origins
    let prep := ProtocolRAMPackedRanked.program L W N (2^gb*(menu+1)) width packed bias classes weights
    let paid := ProtocolRAMPackedRanked.clock L N (2^gb*(menu+1)) width packed bias classes weights
    ∃ out,(prep.seq ((clearedProcedure W base total src (N*cap) γ sink A).seq writeWidths)).Exec mem out
      (paid+(((4+6*total)+(8+16230*(N*cap)))+((4+6*(2*groups*D))+(8+4130*(N*cap))))) ∧
      (∀ x : TaggedShorterSlotWidth.Slot groups D,out (TaggedShorterSlotWidth.index payloadBase x)=
        (TaggedShorterSlotWidth.value pl (TaggedShorterSlotWidth.reportWidth rows w menu γ distinct) x:Word W)) ∧
      (∀ i,decide ((out (addr (.inl i)).val).val≠0)=groupOccupied c bound B M i) ∧
      (∀ sb x,decide ((out (addr (.inr (false,sb,x))).val).val≠0)=groupMask c bound B M pl sb x) ∧
      (∀ sb x,Computability.VPVNP.RAMSerialization.wordBits n (((out (addr (.inr (true,sb,x))).val).val:ℕ):Word n)=
        groupID c bound M hb hw pl sb x) ∧
      (∀ a,a < L.spread→a < base→a≠sink→a≠payloadSink→ out a=mem a) := by
  obtain ⟨out,run,widths,occupied,masks,ids,stored,frame⟩ := publish_stored L width packed bias classes weights left right rows lr mem fit wf gf bf cf xf lf rf wRead gRead
    directory classData copies leftRead rightRead groupCount wideG chronological protectedROM read
    gFit distinct bound copied pl located groupCap boundCap mapCap tableCap widthFit wide menuFits
    typeFits small slotFits hb hw batchFits layoutFit ordered room sinkLow apart input low
    payloadBase payloadSrc payloadSink origins protectedOrigins og saveW saveG saveC saveL saveR
    saveO saveROM following payOrder payRoom paySink payApart payFit payLow
  exact ⟨out,run,widths,occupied,masks,ids,frame⟩

end Hierarchy.ProtocolRAMPackedFinal

end OAI
