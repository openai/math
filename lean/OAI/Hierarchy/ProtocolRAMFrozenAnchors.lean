import OAI.Hierarchy.ProtocolRAMFrozenWidthFrame
import OAI.Hierarchy.TaggedShorterSlotWidthPublish

namespace OAI
/-! # Publish all four physical field families from translated, immutable port anchors -/

namespace Hierarchy.ProtocolRAMFrozenFinal

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat Routing CallPool RAM RAM.DescriptorExpr PhysicalProcedure
open ProtocolRAM TaggedShorterEmitMachine TaggedShorterReportedPublish
open TaggedShorterGroups TaggedShorterReportAdvice
open ProtocolRAMFrozenWidthFrame
open scoped Classical Fin.CommRing

variable {W N m d h lanes : ℕ}

theorem publish_from_anchors_stored {groups D B M n w menu cap rom bits base src sink γ : ℕ}
    (mem : Memory W) (rows : Fin N→ProtocolRAMEmit.Row)
    (width group rank left right : Bank) (cr : Fin N→ℕ) (lr : Bool→Fin N→ℕ)
    (old : Dynamic rows mem width group rank left right cr lr)
    (read : ∀ j : Fin 13,∀ x : ℕ,x<2^bits → (bank rom bits j).read mem (x:Word W)=
      words groups D B M base w menu cap j x)
    (gFit : ∀i,0 < ProtocolRAMReportedPorts.pieces rows w i → (rows i).group < groups) (distinct : Function.Injective fun i=>(rows i).link)
    (bound : ∀g : Fin groups,size rows w menu γ g ≤ D)
    (copied : ∀i,ProtocolRAMReportedPorts.pieces rows w i ≤ cap)
    (cn : ∀ (g : Fin groups) (i : ProtocolRAMReportedPorts.InGroup rows w menu γ g.val),cr i.val =
      ProtocolRAMPortRanks.«prefix» (ProtocolRAMReportedPorts.slotCount rows w menu γ g.val)
        (fun j=>(rows j.val).link) i)
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
    (input : (term (tables rom bits width group rank left right) γ sink).Fits W src)
    (low : (term (tables rom bits width group rank left right) γ sink).Fits W base)
    (payloadBase payloadSrc payloadSink : ℕ) (origins : Bank)
    (og : ∀ g : Fin groups,origins.read mem (g.val:Word W)=((payloadBase+2*g.val*D:ℕ):Word W))
    (saveW : Safe width base sink) (saveG : Safe group base sink) (saveC : Safe rank base sink)
    (saveL : Safe left base sink) (saveR : Safe right base sink)
    (saveO : Safe origins base sink) (saveROM : ∀ j : Fin 13,Safe (bank rom bits j) base sink)
    (following : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D)) ≤ payloadBase)
    (payOrder : payloadBase+2*groups*D ≤ payloadSrc) (payRoom : payloadSrc+10*(N*cap)<2^W)
    (paySink : payloadSink < base) (payApart : ∀x : TaggedShorterSlotWidth.Slot groups D,
      payloadSink≠TaggedShorterSlotWidth.index payloadBase x)
    (payFit : (TaggedShorterSlotWidth.term
      (tables rom bits width group rank left right) origins D γ payloadSink).Fits W payloadSrc)
    (payLow : (TaggedShorterSlotWidth.term
      (tables rom bits width group rank left right) origins D γ payloadSink).Fits W payloadBase) :
    let A := tables rom bits width group rank left right
    let C := capacity (Fin groups) D B M
    let total := C+2*(C*2*D)
    let c := size (groups:=groups) rows w menu γ
    let addr := TaggedShorterScatter.layout C D base layoutFit
    let writeWidths := TaggedShorterSlotWidth.procedure W payloadBase groups D payloadSrc (N*cap) γ payloadSink A origins
    ∃ out, ((clearedProcedure W base total src (N*cap) γ sink A).seq writeWidths).Exec mem out
      (((4+6*total)+(8+16230*(N*cap)))+
        ((4+6*(2*groups*D))+(8+4130*(N*cap)))) ∧
      (∀ x : TaggedShorterSlotWidth.Slot groups D,out (TaggedShorterSlotWidth.index payloadBase x)=
        (TaggedShorterSlotWidth.value pl (TaggedShorterSlotWidth.reportWidth rows w menu γ distinct) x:Word W)) ∧
      (∀ i,decide ((out (addr (.inl i)).val).val≠0)=groupOccupied c bound B M i) ∧
      (∀ sb x,decide ((out (addr (.inr (false,sb,x))).val).val≠0)=groupMask c bound B M pl sb x) ∧
      (∀ sb x,Computability.VPVNP.RAMSerialization.wordBits n (((out (addr (.inr (true,sb,x))).val).val:ℕ):Word n)=
        groupID c bound M hb hw pl sb x) ∧
      (∀ f : TaggedShorterScatter.Field C D,out (addr f).val=(TaggedShorterScatter.contents c bound hb hw pl f:Word W)) ∧
      (∀ a,a < base→a≠sink→a≠payloadSink→ out a=mem a) := by
  intro A C total c addr writeWidths
  obtain ⟨marked,writeBoard,keep,stored⟩ := publish_report_at_framed_stored_live mem rows
    width group rank left right cr lr old read gFit distinct bound copied cn pl located groupCap
    boundCap mapCap tableCap widthFit wide menuFits typeFits small slotFits hb hw batchFits layoutFit
    ordered room sinkLow apart input low
  obtain ⟨occupied,masks,ids⟩ := TaggedShorterScatter.decode_words c bound hb hw pl addr marked
    (by omega) batchFits stored
  have dyn := ProtocolRAMFrozenWidthFrame.dynamic mem marked base sink keep rows width group rank
    left right cr lr old saveW saveG saveC saveL saveR
  have romData := ProtocolRAMFrozenWidthFrame.table mem marked base sink keep saveROM read
  have originsAt (g : Fin groups) : origins.read marked (g.val:Word W)=((payloadBase+2*g.val*D:ℕ):Word W) :=
    (ProtocolRAMFrozenWidthFrame.read mem marked base sink keep origins saveO _).trans (og g)
  have afterBoard : base+total ≤ payloadBase := following
  have payBefore : payloadSink < payloadSrc := by omega
  obtain ⟨final,writeWords,widths,frame⟩ := TaggedShorterSlotWidth.publish_report_at_live marked rows
    width group rank left right origins cr lr dyn
    romData originsAt gFit distinct copied pl located
    tableCap widthFit wide menuFits typeFits (by omega) slotFits payOrder payRoom payBefore payApart payFit payLow
  have retains (f : TaggedShorterScatter.Field C D) : final (addr f).val=marked (addr f).val := by
    have bounds : base≤(addr f).val ∧ (addr f).val < base+total := by
      change base ≤ base+(TaggedShorterScatter.fieldIndex C D f).val ∧
        base+(TaggedShorterScatter.fieldIndex C D f).val < base+(C+2*(C*2*D))
      have := (TaggedShorterScatter.fieldIndex C D f).isLt
      omega
    exact frame _ (.inl (by omega)) (.inl (by omega)) (by omega)
  refine ⟨final,?_,widths,?_,?_,?_,fun f=>(retains f).trans (stored f),?_⟩
  · intro P R K machine pc reg pub exit installed data cfg raw entry eq
    exact Procedure.Exec.then writeBoard writeWords machine pc reg pub exit installed data cfg raw entry eq
  · intro i
    rw [retains]
    exact occupied i
  · intro sb x
    rw [retains]
    exact masks sb x
  · intro sb x
    rw [retains]
    exact ids sb x
  · intro a lo ns np
    have same := frame a (Or.inl (by omega)) (Or.inl (by omega)) np
    exact same.trans (keep a lo ns)

theorem publish_from_anchors {groups D B M n w menu cap rom bits base src sink γ : ℕ}
    (mem : Memory W) (rows : Fin N→ProtocolRAMEmit.Row)
    (width group rank left right : Bank) (cr : Fin N→ℕ) (lr : Bool→Fin N→ℕ)
    (old : Dynamic rows mem width group rank left right cr lr)
    (read : ∀ j : Fin 13,∀ x : ℕ,x<2^bits → (bank rom bits j).read mem (x:Word W)=
      words groups D B M base w menu cap j x)
    (gFit : ∀i,0 < ProtocolRAMReportedPorts.pieces rows w i → (rows i).group < groups) (distinct : Function.Injective fun i=>(rows i).link)
    (bound : ∀g : Fin groups,size rows w menu γ g ≤ D)
    (copied : ∀i,ProtocolRAMReportedPorts.pieces rows w i ≤ cap)
    (cn : ∀ (g : Fin groups) (i : ProtocolRAMReportedPorts.InGroup rows w menu γ g.val),cr i.val =
      ProtocolRAMPortRanks.«prefix» (ProtocolRAMReportedPorts.slotCount rows w menu γ g.val)
        (fun j=>(rows j.val).link) i)
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
    (input : (term (tables rom bits width group rank left right) γ sink).Fits W src)
    (low : (term (tables rom bits width group rank left right) γ sink).Fits W base)
    (payloadBase payloadSrc payloadSink : ℕ) (origins : Bank)
    (og : ∀ g : Fin groups,origins.read mem (g.val:Word W)=((payloadBase+2*g.val*D:ℕ):Word W))
    (saveW : Safe width base sink) (saveG : Safe group base sink) (saveC : Safe rank base sink)
    (saveL : Safe left base sink) (saveR : Safe right base sink)
    (saveO : Safe origins base sink) (saveROM : ∀ j : Fin 13,Safe (bank rom bits j) base sink)
    (following : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D)) ≤ payloadBase)
    (payOrder : payloadBase+2*groups*D ≤ payloadSrc) (payRoom : payloadSrc+10*(N*cap)<2^W)
    (paySink : payloadSink < base) (payApart : ∀x : TaggedShorterSlotWidth.Slot groups D,
      payloadSink≠TaggedShorterSlotWidth.index payloadBase x)
    (payFit : (TaggedShorterSlotWidth.term
      (tables rom bits width group rank left right) origins D γ payloadSink).Fits W payloadSrc)
    (payLow : (TaggedShorterSlotWidth.term
      (tables rom bits width group rank left right) origins D γ payloadSink).Fits W payloadBase) :
    let A := tables rom bits width group rank left right
    let C := capacity (Fin groups) D B M
    let total := C+2*(C*2*D)
    let c := size (groups:=groups) rows w menu γ
    let addr := TaggedShorterScatter.layout C D base layoutFit
    let writeWidths := TaggedShorterSlotWidth.procedure W payloadBase groups D payloadSrc (N*cap) γ payloadSink A origins
    ∃ out, ((clearedProcedure W base total src (N*cap) γ sink A).seq writeWidths).Exec mem out
      (((4+6*total)+(8+16230*(N*cap)))+
        ((4+6*(2*groups*D))+(8+4130*(N*cap)))) ∧
      (∀ x : TaggedShorterSlotWidth.Slot groups D,out (TaggedShorterSlotWidth.index payloadBase x)=
        (TaggedShorterSlotWidth.value pl (TaggedShorterSlotWidth.reportWidth rows w menu γ distinct) x:Word W)) ∧
      (∀ i,decide ((out (addr (.inl i)).val).val≠0)=groupOccupied c bound B M i) ∧
      (∀ sb x,decide ((out (addr (.inr (false,sb,x))).val).val≠0)=groupMask c bound B M pl sb x) ∧
      (∀ sb x,Computability.VPVNP.RAMSerialization.wordBits n (((out (addr (.inr (true,sb,x))).val).val:ℕ):Word n)=
        groupID c bound M hb hw pl sb x) ∧
      (∀ a,a < base→a≠sink→a≠payloadSink→ out a=mem a) := by
  obtain ⟨out,run,widths,occupied,masks,ids,stored,frame⟩ := publish_from_anchors_stored mem rows width group rank left right cr lr old read gFit distinct bound copied cn pl located
    groupCap boundCap mapCap tableCap widthFit wide menuFits typeFits small slotFits hb hw
    batchFits layoutFit ordered room sinkLow apart input low payloadBase payloadSrc payloadSink
    origins og saveW saveG saveC saveL saveR saveO saveROM following payOrder payRoom paySink
    payApart payFit payLow
  exact ⟨out,run,widths,occupied,masks,ids,frame⟩


end Hierarchy.ProtocolRAMFrozenFinal

end OAI
