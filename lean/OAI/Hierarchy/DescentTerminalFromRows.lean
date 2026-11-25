import OAI.Hierarchy.DescentTerminalReached

namespace OAI
/-! # A fixed homogeneous host for a common reached graph and its executed native chip -/
namespace Hierarchy.DescentTerminalReadout
open ThreeFlat Routing SortNetwork Diagonal TraceRows TraceBanks
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory ProtocolRAM TaggedShorterControlHistory
open Catalyst CatalystSubstitution Tagged Tagged.SortLift TaggedShorterHistoryOrder
open DescentTerminalRAM DescentTerminalHost DescentTerminalPorts DescentTerminalThreshold DescentTerminalLast
open Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing BigOperators
noncomputable section

section
variable {F B : Type} [Field F] [Fintype B] {w p r k f S u m n s steps parts arity dest rows word bins W : ℕ}
  (stages : Fin steps→Stage (2^m)) (field : Fin parts→ℕ)
  (cover : (∑j,field j)=n+RecordWidth (w+1)) (fitFields : ∀j,field j≤n+s)
  (widths : Fin arity→ℕ) (Y : Approximation F arity (Tagged.pins (n+s) (n+s)))
  (cpu : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
  (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1)) (addr : Fin u→Word w)
  (init : Fin S×Fin (w+1)→(Catalyst.Port dest widths⊕B)⊕Bool)
  (scalar : Fin bins→F) (links : DescentTerminalPaidFactors.Pin rows word bins W→
    (Catalyst.Port dest widths⊕B)⊕Observed u w)

private def controllerValue (x : Catalyst.Port dest widths→Bool) : F :=
  exactValue _ (nativeHost stages field cover fitFields widths Y cpu hw hp st hs ht addr init scalar links) x

private def controllerPrice : ℕ :=
  hostSize (nativeHost stages field cover fitFields widths Y cpu hw hp st hs ht addr init scalar links)

private theorem controllerPrice_bound (payload : 0<word) {K : ℕ}
    (wordFit : RecordWidth (w+1)≤K*(n+s+1))
    (cheap : ∀i,TaggedShorterCheapCPU.Cheap (cpu.code i)) :
    controllerPrice stages field cover fitFields widths Y cpu hw hp st hs ht addr init scalar links ≤
      4*((f+1)*TaggedShorterClock.unitPrice w p r+2^m*(20000*(w+1))+
        (4*(2^m*(50*(w+1)+11)+2*2^m+1)+1))+1+9*(rows*word)+bins*W+
      (Fintype.card B+f*((5+r)*(w+1))+u*(w+1)+(steps+1)*(2^m*RecordWidth (w+1)))+
      Fintype.card (Catalyst.Port dest widths)+1000*(K+parts+1)*
        (DescentTerminalHost.SortBank.localCount stages*2^n+2^(n+s))*(n+s+1) :=
  nativeHost_price stages field cover fitFields widths Y cpu hw hp st hs ht addr init scalar links
    payload wordFit cheap
end

section
variable {F : Type} [Field F] {A T P : Type} [Fintype A] [Fintype T]
variable {w p r k f S u m n s steps parts arity dest rows word bins W geo : ℕ} {bits : P→ℕ}

variable (stages : Fin steps→Stage (2^m))
    (field : Fin parts→ℕ) (cover : (∑j,field j)=n+RecordWidth (w+1)) (widthFit : ∀j,field j≤n+s)
    (width : Fin arity→ℕ) (Y : Approximation F arity (Tagged.pins (n+s) (n+s)))
    (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1)) (addr : Fin u→Word w)
    (init : Fin S×Fin (w+1)→(Catalyst.Port dest width ⊕ Choice A rows word) ⊕ Bool)
    (scalar : Fin bins→F)
    (dataPin : DescentTerminalPaidFactors.Pin rows word bins W→
      (Catalyst.Port dest width ⊕ Choice A rows word) ⊕ Observed u w)

set_option maxHeartbeats 800000 in
private theorem controller_contraction [Nonempty (Fin parts)] (small : ∀i b,(stages i).length b≤2^n)
    (sorts : Sorts (List.ofFn stages) (Fin (2^RecordWidth (w+1)))) (fits : S+(f+u)≤2^m)
    (memRoom : S≤2^w) (x : Catalyst.Port dest width→Bool) (outer : Ports bits)
    (base : (Choice A rows word→Bool)→ℕ→Word w)
    (readInit : ∀b i,Sum.elim (Sum.elim x b) id (init i)=TraceWords.bits (wide (base b i.1.val)) i.2)
    (out : (Choice A rows word→Bool)→Memory w) (exec : ∀b,∃ t cfg result,t<f ∧
      RAM.advance M.program t (M.program.start st) (initialMemory S (base b))=some (cfg,out b) ∧ M.program.step cfg=.finish result)
    (decode : (RowBit rows word→Bool)→(A→Bool)→Option T)
    (unique : ∀pay t,∃! a,decode pay a=some t)
    (graph : T→Network geo P bits) (table : ∀t,(graph t).Tables F) (edgeCode : ∀t,(graph t).Edge ↪ ℕ)
    (volume : ∀t,(∑e,(graph t).width e)≤rows*word) (weight : T→F)
    (queries : T→ℕ) (countFit : ∀t,queries t<2^W) (key : ∀t,(RowBit rows word→Bool)→Fin (queries t)→Fin bins)
    (entries : ∀t pay,(∏ i,scalar (key t pay i))=weight t*∏v,(graph t).read (table t)
      (takeBits (graph t) (denseBits (graph t) (edgeCode t) (volume t)) pay) outer v)
    (admit : ∀a t pay,decode pay a=some t→
      resultPins addr dataPin x (Sum.elim a pay) (out (Sum.elim a pay))=
      DescentTerminalPaidFactors.factorPins
        (fun i=>DescentTerminalDenseMask.valid word (∑e,(graph t).width e) i.val) pay (countDigit (key t pay)))
    (reject : ∀a pay,decode pay a=none→∃cut flag b i, (∀j,cut j≤word) ∧ scalar b=0 ∧ flag (b,i)=true ∧
      resultPins addr dataPin x (Sum.elim a pay) (out (Sum.elim a pay))=
      DescentTerminalPaidFactors.factorPins cut pay flag) :
    controllerValue stages field cover widthFit width Y M hw hp st hs ht addr init scalar dataPin x =
      ∑t,weight t*(graph t).value (table t) outer :=
  payload_contraction stages field cover widthFit width Y M hw hp st hs ht addr init scalar dataPin
    small sorts fits memRoom x outer base readInit out exec decode unique graph table edgeCode volume weight
    queries countFit key entries admit reject
end

attribute [local irreducible] DescentTerminalLast.program DescentTerminalLast.ticks complete ProtocolRAM.machine

variable {F : Type} [Field F] {A T I P : Type} [Fintype A] [Fintype T] [Fintype I]
  {w S0 m n s steps parts arity dest rows slots word bins W cut stop geo : ℕ} {bits : P→ℕ}
variable (L : Tape) (C : DescentCensusRAM.Banks w slots bins) (ready : Ready L C cut stop rows word)
variable (Q : Procedure w) (stages : Fin steps→Stage (2^m)) (field : Fin parts→ℕ)
    (cover : (∑j,field j)=n+RecordWidth (w+1)) (fitFields : ∀j,field j≤n+s)
    (widths : Fin arity→ℕ) (Y : Approximation F arity (Tagged.pins (n+s) (n+s)))
local notation "Raw" => RowBit rows word→Bool
local notation "Input" => Choice A rows word→Bool
local notation "proc" => complete L C (cut:=cut) (stop:=stop) (rows:=rows) (word:=word) Q
local notation "M" => ProtocolRAM.machine (w:=w) proc (stop:Word w)
local notation "B" => Fintype.card I+bins+1
local notation "U" => rows+B
variable (hw : 3≤w+1) (hp : (complete L C (cut:=cut) (stop:=stop) (rows:=rows) (word:=word) Q).labels+3≤2^(w+1)) (st : Word w)
    (hs : S0≤2^(w+1)) (time : ℕ)
local notation "fuel" => time+ticks L C rows word+3
variable (ht : time+ticks L C rows word+3+(rows+(Fintype.card I+bins+1))≤2^(w+1)) (seed : I→ℕ) (before : ∀i,seed i<cut)
    (short : depth word≤w+1) (width : W≤w+1)
    (init : Fin S0×Fin (w+1)→(Catalyst.Port dest widths⊕Choice A rows word)⊕Bool)
    (original : I→F) (table : Fin bins→F)
local notation "addr" => (fun i=>(observations (fun j:Fin rows=>cut+Fin.val j) seed (fun j:Fin bins=>C.bins+Fin.val j) stop i:Word w))
local notation "links" => DescentTerminalReadout.pins (I:=I) (E:=Catalyst.Port dest widths)
  (A:=A) (rows:=rows) (word:=word) (bins:=bins) (W:=W) (w:=w) short width
local notation "valueAt" => controllerValue («B»:=Choice A rows word) (rows:=rows) (word:=word) (W:=W)
  (w:=w) (p:=Procedure.labels proc+3) (r:=Procedure.registers proc+1) (k:=Procedure.slots proc)
  (f:=fuel) (u:=U) (S:=S0) (bins:=B) stages field cover fitFields widths Y M hw hp st hs ht
  addr init (scalar original table) links
local notation "priceHere" => controllerPrice («B»:=Choice A rows word) (rows:=rows) (word:=word) (W:=W)
  (w:=w) (p:=Procedure.labels proc+3) (r:=Procedure.registers proc+1) (k:=Procedure.slots proc)
  (f:=fuel) (u:=U) (S:=S0) (bins:=B) stages field cover fitFields widths Y M hw hp st hs ht
  addr init (scalar original table) links

set_option maxHeartbeats 800000 in
include ready hp ht before in
theorem from_factor_rows [Nonempty (Fin parts)] (small : ∀i b,(stages i).length b≤2^n)
    (sorts : Sorts (List.ofFn stages) (Fin (2^RecordWidth (w+1)))) (packed : S0+(fuel+U)≤2^m)
    (initialRoom : S0≤2^w) (x : Catalyst.Port dest widths→Bool) (outer : Ports bits)
    (base : Input→ℕ→Word w)
    (root : ∀b i,Sum.elim (Sum.elim x b) id (init i)=TraceWords.bits (wide (base b i.1.val)) i.2)
    (reached : Input→Memory w) (issued : ∀z,Q.Exec (initialMemory S0 (base z)) (reached z) time)
    (cheapQ : CheapCode Q) (decode : Raw→(A→Bool)→Option T) (one : ∀pay t,∃!a,decode pay a=some t)
    (graph : T→Network geo P bits) (tables : ∀t,(graph t).Tables F) (edges : ∀t,(graph t).Edge ↪ ℕ)
    (volume : ∀t,(∑e,(graph t).width e)≤rows*word) (pos : 0<word) (posW : 0<W)
    (seedCount : T→I→ℕ) (key : T→Raw→Fin slots→Fin bins) (seedFit : ∀t i,seedCount t i<2^w)
    (countsFit : ∀t,Fintype.card (DescentTerminalSeedFactors.Occurs (seedCount t) (Fin slots))<2^W)
    (cells : InputCells (word:=word) L reached decode (fun t=>∑e,(graph t).width e) seedCount key seed)
    (weight : T→F) (factors : ∀t pay,
      (∏i,original i^seedCount t i)*(∏j,table (key t pay j))=weight t*∏v,(graph t).read (tables t)
        (takeBits (graph t) (denseBits (graph t) (edges t) (volume t)) pay) outer v) :
    valueAt x=∑t,weight t*(graph t).value (tables t) outer := by
  refine controller_contraction (A:=A) (w:=w) (p:=(proc).labels+3) (r:=(proc).registers+1) (k:=(proc).slots)
    (f:=fuel) (u:=U) (S:=S0) (rows:=rows) (word:=word) (W:=W) (bins:=B)
    stages field cover fitFields widths Y M hw hp st hs ht addr init
    (scalar original table) links small sorts packed initialRoom x outer base root
    (finalMem L C ready reached)
    (fun z=>(full_exec L C ready Q (fun b=>initialMemory S0 (base b)) reached time issued cheapQ st z).1)
    decode one graph tables edges volume weight _ countsFit
    (fun t p=>requests (seedCount t) (key t p)) ?_ ?_ ?_
  · intro t pay;rw [requests_eval];exact factors t pay
  · exact full_admit L C ready x seed before short width pos reached decode _ seedCount key cells seedFit
  · exact full_reject L C ready x seed before short width reached decode _ seedCount key cells original table
      posW (by have:=ready.final;have:=C.finish;have:=ready.binsPos;omega)

set_option maxHeartbeats 800000 in
include ready hp ht before in
theorem from_rows [Nonempty (Fin parts)] (small : ∀i b,(stages i).length b≤2^n)
    (sorts : Sorts (List.ofFn stages) (Fin (2^RecordWidth (w+1)))) (packed : S0+(fuel+U)≤2^m)
    (initialRoom : S0≤2^w) (x : Catalyst.Port dest widths→Bool) (outer : Ports bits)
    (base : Input→ℕ→Word w)
    (root : ∀b i,Sum.elim (Sum.elim x b) id (init i)=TraceWords.bits (wide (base b i.1.val)) i.2)
    (reached : Input→Memory w) (issued : ∀z,Q.Exec (initialMemory S0 (base z)) (reached z) time)
    (cheapQ : CheapCode Q) (decode : Raw→(A→Bool)→Option T) (one : ∀pay t,∃!a,decode pay a=some t)
    (graph : T→Network geo P bits) (tables : ∀t,(graph t).Tables F) (edges : ∀t,(graph t).Edge ↪ ℕ)
    (volume : ∀t,(∑e,(graph t).width e)≤rows*word) (pos : 0<word) (posW : 0<W)
    (seedCount : T→I→ℕ) (key : T→Raw→Fin slots→Fin bins) (seedFit : ∀t i,seedCount t i<2^w)
    (countsFit : ∀t,Fintype.card (DescentTerminalSeedFactors.Occurs (seedCount t) (Fin slots))<2^W)
    (cells : InputCells (word:=word) L reached decode (fun t=>∑e,(graph t).width e) seedCount key seed)
    (weight : T→F) (originals : ∀t,weight t=∏i,original i^seedCount t i)
    (localRows : ∀t pay,(∏j,table (key t pay j))=∏v,(graph t).read (tables t)
      (takeBits (graph t) (denseBits (graph t) (edges t) (volume t)) pay) outer v) :
    valueAt x=∑t,weight t*(graph t).value (tables t) outer := by
  apply from_factor_rows L C ready Q stages field cover fitFields widths Y hw hp st hs time ht seed
    before short width init original table small sorts packed initialRoom x outer base root reached
    issued cheapQ decode one graph tables edges volume pos posW seedCount key seedFit countsFit cells weight
  intro t pay
  rw [originals,localRows]

set_option maxHeartbeats 800000 in
include ready hp ht in
omit ready in
theorem from_rows_price (payload : 0<word) {K : ℕ} (wordFit : RecordWidth (w+1)≤K*(n+s+1))
    (cheapQ : CheapCode Q) :
    priceHere≤4*((fuel+1)*TaggedShorterClock.unitPrice w ((proc).labels+3) ((proc).registers+1)+
      2^m*(20000*(w+1))+(4*(2^m*(50*(w+1)+11)+2*2^m+1)+1))+1+9*(rows*word)+B*W+
      (Fintype.card (Choice A rows word)+fuel*((5+((proc).registers+1))*(w+1))+U*(w+1)+
        (steps+1)*(2^m*RecordWidth (w+1)))+
      Fintype.card (Catalyst.Port dest widths)+1000*(K+parts+1)*
        (DescentTerminalHost.SortBank.localCount stages*2^n+2^(n+s))*(n+s+1) := by
  have cheap : CheapCode proc := by
    unfold complete
    exact @cheap_seq w Q (DescentTerminalLast.program L C cut stop rows word)
      cheapQ (DescentTerminalLast.cheap L C cut stop rows word)
  exact controllerPrice_bound («B»:=Choice A rows word) (p:=Procedure.labels proc+3)
    (r:=Procedure.registers proc+1) (k:=Procedure.slots proc) (f:=fuel) (u:=U) (S:=S0) (bins:=B)
    stages field cover fitFields widths Y M hw hp st hs ht addr init (scalar original table) links
    payload wordFit (machine_cheap proc (stop:Word w) cheap)

end
end Hierarchy.DescentTerminalReadout

end OAI
