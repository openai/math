import OAI.Hierarchy.DescentFixedISASortTariff
import OAI.Hierarchy.CheapISAExecution
import OAI.Hierarchy.CheapISATerminalPins
import OAI.Hierarchy.DescentTerminalFromChip
import OAI.Hierarchy.DescentTerminalWeightedContraction

namespace OAI
/-! # The 72-label terminal host for the original controller and its labelled output bits -/
namespace Hierarchy.DescentTerminalFixedISAHost
open DescentTerminalReadout DescentTerminalChipRuntime DescentTerminalChipPins
open ThreeFlat Routing SortNetwork Diagonal TraceRows TraceBanks
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory ProtocolRAM TaggedShorterControlHistory
open Catalyst CatalystSubstitution Tagged Tagged.SortLift TaggedShorterHistoryOrder
open DescentTerminalRAM DescentTerminalHost DescentTerminalPorts DescentTerminalThreshold DescentTerminalLast
open Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
private theorem extended_width (w : ℕ) : 3 ≤ CheapISA.width w+1 := by
  unfold CheapISA.width
  omega

private theorem labels_fit (w : ℕ) (positive : 0< w) : 72 ≤ 2^(CheapISA.width w+1) := by
  exact (by decide : 72 ≤ 2^7).trans (Nat.pow_le_pow_right (by decide) (by unfold CheapISA.width; omega))

/-- Two spare source instruction slots pay for both clock bookends after translation. -/
theorem clock_fits {w fuel observations : ℕ} (room : fuel+observations+2 ≤ 2^w) :
    CheapISA.hostFuel fuel+observations ≤ 2^(CheapISA.width w+1) :=
  CheapISA.hostFuel_room room

private theorem header_room {w p r S : ℕ} (hp : p ≤ 2^(w+1)) (hr : r ≤ 2^(w+1))
    (room : S ≤ 2^w) : CheapISA.dataBase p r+S ≤ 2^CheapISA.width w :=
  (Nat.add_le_add_left room _).trans (CheapISA.fits_extent hp hr).le

private abbrev joinedProgram {I : Type} {w slots bins : ℕ} (D : Columns (I:=I))
    (layout : DescentTerminalChipRuntime.Layout) (banks : DescentTerminalChipRuntime.Banks)
    (C : DescentCensusRAM.Banks w slots bins) (Q : Procedure w) (pool cut stop rows word : ℕ) :=
  complete (D.tape layout pool) C (cut:=cut) (stop:=stop) (rows:=rows) (word:=word)
    (Q.seq (DescentTerminalChipRuntime.program layout banks w pool slots))

attribute [local irreducible] DescentTerminalLast.program DescentTerminalLast.ticks
  DescentTerminalChipRuntime.program DescentTerminalChipRuntime.clocks Procedure.seq complete ProtocolRAM.machine
  CheapISA.machine

variable {F : Type} [Field F] {A T I P : Type} [Fintype A] [Fintype T] [Fintype I]
  {w S0 m n s steps parts arity dest rows slots word bins W cut stop geo K Cap q piece : ℕ} {bits : P→ℕ}
local notation "N" => K*Cap
local notation "d" => q*(Cap*piece)
local notation "Bits" => Inputs K Cap q piece
variable (D : Columns (I:=I)) (P0 : DescentTerminalChipRuntime.Layout) (L0 : DescentTerminalChipRuntime.Banks)
    (chipRoom : Room P0 L0 w (K*Cap) slots) (dataRoom : q*(Cap*piece)≤ w) (positive : 0< w)
local notation "L" => D.tape P0 N
variable (C : DescentCensusRAM.Banks w slots bins) (ready : Ready (D.tape P0 (K*Cap)) C cut stop rows word)
variable (Q : Procedure w) (stages : Fin steps→ Stage (2^m)) (field : Fin parts→ℕ)
    (cover : (∑j,field j)=n+RecordWidth (CheapISA.width w+1)) (fitFields : ∀j,field j≤ n+s)
    (widths : Fin arity→ℕ) (Y : Approximation F arity (Tagged.pins (n+s) (n+s)))
local notation "Raw" => RowBit rows word→ Bool
local notation "Input" => Choice (A⊕Bits) rows word→ Bool
local notation "fed" => Q.seq (DescentTerminalChipRuntime.program P0 L0 w N slots)
local notation "proc" => joinedProgram D P0 L0 C Q (K*Cap) cut stop rows word
local notation "M" => ProtocolRAM.machine proc (stop:Word w)
local notation "B" => Fintype.card I+bins+1
local notation "U" => rows+B
local notation "regs" => ((proc).registers+1)
local notation "pcs" => ((proc).labels+3)
local notation "seedWords" => (CheapISA.dataBase pcs regs+S0)
variable (hp : (joinedProgram D P0 L0 C Q (K*Cap) cut stop rows word).labels+3 ≤ 2^(w+1))
    (hr : (joinedProgram D P0 L0 C Q (K*Cap) cut stop rows word).registers+1 ≤ 2^(w+1)) (st : Word w)
    (initialRoom : S0 ≤ 2^w) (time : ℕ)
local notation "fuel" => time+clocks N slots+ticks L C rows word+3
local notation "clock" => CheapISA.hostFuel fuel
variable (ht : CheapISA.hostFuel (time+clocks (K*Cap) slots+ticks (D.tape P0 (K*Cap)) C rows word+3)+
      (rows+(Fintype.card I+bins+1))≤2^(CheapISA.width w+1)) (before : ∀i,D.seed i< cut)
    (short : depth word≤ w+1) (width : W≤ w+1)
    (init : Fin S0×Fin (w+1)→(Catalyst.Port dest widths⊕Choice (A⊕Inputs K Cap q piece) rows word)⊕Bool)
    (seedCircuit : BitNetwork F (Fintype.card (Choice (A⊕Inputs K Cap q piece) rows word))) (original : I→ F) (table : Fin bins→ F)
local notation "addr" => (fun i=>(observations (fun j:Fin rows=>cut+Fin.val j) D.seed (fun j:Fin bins=>C.bins+Fin.val j) stop i:Word w))
local notation "links" => DescentTerminalReadout.pins (I:=I) (E:=Catalyst.Port dest widths)
  (A:=A⊕Inputs K Cap q piece) (rows:=rows) (word:=word) (bins:=bins) (W:=W) (w:=w) short width
local notation "target" => CheapISA.machine w pcs regs (M).entry
local notation "header" => CheapISA.headerPin regs (CheapISA.ROM M) init
local notation "observed" => CheapISA.translatedAddr pcs regs addr
local notation "data" => CheapISA.translatedPin links

/-- The host reads the immutable instruction columns, its private register bank, and
the original variable header from consecutive physical cells. Its CPU has 72 labels
and 13 registers for every controller. -/
def onProgram :=
  DescentTerminalWeightedHost.host stages field cover fitFields widths Y target
    (extended_width w) (labels_fit w positive) (CheapISA.wide st)
    ((header_room hp hr initialRoom).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))
    ht observed header seedCircuit (scalar original table) data

local notation "host" => onProgram (D:=D) (P0:=P0) (L0:=L0) (positive:=positive) (C:=C)
  (Q:=Q) (stages:=stages) (field:=field) (cover:=cover) (fitFields:=fitFields) (widths:=widths)
  (Y:=Y) (hp:=hp) (hr:=hr) (st:=st) (initialRoom:=initialRoom) (time:=time) (ht:=ht)
  (short:=short) (width:=width) (init:=init) (seedCircuit:=seedCircuit) (original:=original) (table:=table)

set_option maxHeartbeats 800000 in
include chipRoom ready before in
theorem contraction [Nonempty (Fin parts)] (small : ∀i b,(stages i).length b≤2^n)
    (sorts : Sorts (List.ofFn stages) (Fin (2^RecordWidth (CheapISA.width w+1)))) (packed : seedWords+(clock+U)≤2^m)
    (x : Catalyst.Port dest widths→ Bool) (outer : Ports bits)
    (base : Input→ℕ→ Word w)
    (root : ∀b i,Sum.elim (Sum.elim x b) id (init i)=TraceWords.bits (wide (base b i.1.val)) i.2)
    (m0 : Input→ Memory w) (earlier : ∀z,Q.Exec (initialMemory S0 (base z)) (m0 z) time)
    (cheap : CheapCode Q) (prior : Raw→(A→ Bool)→ Option T) (single : ∀x t,∃!z,prior x z=some t)
    (contents : T→ Raw→ Content K Cap q piece)
    (graph : T→ Network geo P bits) (tables : ∀t,(graph t).Tables F) (edges : ∀t,(graph t).Edge ↪ ℕ)
    (volume : ∀t,(∑e,(graph t).width e)≤ rows*word) (pos : 0< word) (posW : 0< W)
    (seedCount : T→ I→ℕ) (key : T→ Raw→ Fin slots→ Fin bins) (seedFit : ∀t i,seedCount t i<2^w)
    (countsFit : ∀t,Fintype.card (DescentTerminalSeedFactors.Occurs (seedCount t) (Fin slots))<2^W)
    (mounted : Current D P0 L0 prior contents (fun t=>∑e,(graph t).width e) seedCount key m0)
    (weight : T→ F) (factors : ∀z t pay,finalChoice dataRoom prior contents pay z=some t→
      TypedWiring.value seedCircuit (Sum.elim z pay)*
        ((∏i,original i^seedCount t i)*(∏j,table (key t pay j)))=weight t*∏v,(graph t).read (tables t)
        (takeBits (graph t) (denseBits (graph t) (edges t) (volume t)) pay) outer v) :
    exactValue _ host x=∑t,weight t*(graph t).value (tables t) outer := by
  obtain ⟨execute,code⟩ := combined_run P0 L0 chipRoom m0 Q
    (fun b=>initialMemory S0 (base b)) time earlier cheap
  let final0 := finished (slots:=slots) P0 L0 m0
  let final := DescentTerminalReadout.finalMem L C ready final0
  let dec := finalChoice dataRoom prior contents
  have source (z : Input) := full_exec L C ready fed (fun b=>initialMemory S0 (base b)) final0
    (time+clocks N slots) execute code st z
  obtain ⟨image,issued,reads⟩ := CheapISA.translated_clock (A:=Input) (S:=S0) (sourceFuel:=fuel) M st base final hp hr
    (source (fun _=>false)).2 (fun z=>(source z).1)
  have cells := input_cells D P0 L0 chipRoom dataRoom positive prior contents _ seedCount key m0 mounted
  let headerData := fun b=>CheapISA.bankHeader regs (CheapISA.ROM M) (base b)
  have readback (b : Input) :=
    CheapISA.resultPins_translated pcs regs addr links x b (final b) (image b) hp hr (reads b)
  unfold onProgram
  refine DescentTerminalWeightedHost.contraction stages field cover fitFields widths Y target _ _
    (CheapISA.wide st) _ ht observed header seedCircuit (scalar original table) data
    small sorts packed (header_room hp hr initialRoom) x outer headerData
    (fun b=>CheapISA.headerPin_read regs (CheapISA.ROM M) init (Sum.elim x b) (base b) (root b))
    image issued dec (choice_once dataRoom prior contents single) graph tables edges volume weight _ countsFit
    (fun t pay=>requests (seedCount t) (key t pay)) ?_ ?_ ?_
  · intro a t pay ok
    rw [requests_eval]
    exact factors a t pay ok
  · intro a t pay ok
    rw [readback]
    exact full_admit L C ready x D.seed before short width pos final0 dec _ seedCount key cells seedFit a t pay ok
  · intro a pay bad
    obtain ⟨lengths,flag,b,i,fit,zero,on,wires⟩ :=
      full_reject L C ready x D.seed before short width final0 dec _ seedCount key cells original table
        posW (by have := ready.final; have := C.finish; have := ready.binsPos; omega) a pay bad
    exact ⟨lengths,flag,b,i,fit,zero,on,(readback (Sum.elim a pay)).trans wires⟩

theorem price (payload : 0< word) {K₁ : ℕ} (wordFit : RecordWidth (CheapISA.width w+1) ≤ K₁*(n+s+1)) :
    hostSize host ≤
      4*((seedCircuit.cells+seedCircuit.internal)+(clock+1)*TaggedShorterClock.unitPrice (CheapISA.width w) 72 13+
        2^m*(20000*(CheapISA.width w+1))+(4*(2^m*(50*(CheapISA.width w+1)+11)+2*2^m+1)+1))+
      1+9*(rows*word)+B*W+
      (Fintype.card (Choice (A⊕Bits) rows word)+clock*((5+13)*(CheapISA.width w+1))+U*(CheapISA.width w+1)+
        (steps+1)*(2^m*RecordWidth (CheapISA.width w+1)))+
      Fintype.card (Catalyst.Port dest widths)+1000*(K₁+parts+1)*
        (DescentTerminalHost.SortBank.localCount stages*2^n+2^(n+s))*(n+s+1) := by
  exact DescentTerminalWeightedHost.price stages field cover fitFields widths Y target _ _ (CheapISA.wide st)
    _ ht observed header seedCircuit (scalar original table) data payload wordFit (CheapISA.machine_cheap w pcs regs (M).entry)

/-- Every original controller uses the same CPU and chronological sorting rate. -/
theorem priced (payload : 0<word) {K₁ : ℕ}
    (wordFit : RecordWidth (CheapISA.width w+1) ≤ K₁*(n+s+1)) (depth : steps ≤ 4^7) :
    hostSize host ≤
      4*(seedCircuit.cells+seedCircuit.internal)+9*(rows*word)+B*W+
      Fintype.card (Choice (A⊕Bits) rows word)+Fintype.card (Catalyst.Port dest widths)+
      1000*(K₁+parts+1)*(DescentTerminalHost.SortBank.localCount stages*2^n+2^(n+s))*(n+s+1)+
      DescentCompiler.fixedISAPrice*(clock+1+2^m+U)*(CheapISA.width w+1) := by
  apply Nat.le_trans ?_ (DescentCompiler.fixed_isa_tariff (CheapISA.width w) m clock steps
    (seedCircuit.cells+seedCircuit.internal) rows word B W (Fintype.card (Choice (A⊕Bits) rows word)) U
    (Fintype.card (Catalyst.Port dest widths))
    (1000*(K₁+parts+1)*(DescentTerminalHost.SortBank.localCount stages*2^n+2^(n+s))*(n+s+1)) depth)
  exact price (D:=D) (P0:=P0) (L0:=L0) (positive:=positive) (C:=C)
    (Q:=Q) (stages:=stages) (field:=field) (cover:=cover) (fitFields:=fitFields) (widths:=widths)
    (Y:=Y) (hp:=hp) (hr:=hr) (st:=st) (initialRoom:=initialRoom) (time:=time) (ht:=ht)
    (short:=short) (width:=width) (init:=init) (seedCircuit:=seedCircuit) (original:=original) (table:=table)
    payload wordFit

section PhysicalSort
open DescentCompiler
variable (h rate : ℕ) (height : 4 ≤ h) (wordBound : w ≤ rate*h)
    (room : CheapISA.dataBase ((joinedProgram D P0 L0 C Q (K*Cap) cut stop rows word).labels+3)
      ((joinedProgram D P0 L0 C Q (K*Cap) cut stop rows word).registers+1)+S0+
      (CheapISA.hostFuel (time+clocks (K*Cap) slots+ticks (D.tape P0 (K*Cap)) C rows word+3)+
        (rows+(Fintype.card I+bins+1))) ≤ 2^(3*h))
    (Y₀ : Approximation F arity (Tagged.pins h h))

local notation "records" => (seedWords+(clock+U))
local notation "recordBits" => (RecordWidth (CheapISA.width w+1))
local notation "labels" => (Fin (2^recordBits))
local notation "ticket" => (terminal_history_order h records room)
local notation "schedule" => (DescentTerminalChosenSort.stages labels height (ticket).1 (ticket).2.1)
local notation "slices" => (TaggedWidthSlices.width (h+recordBits) h)
local notation "scale" => (7*(rate+6))

private theorem physical_fields (wordWidth heightBase coeff : ℕ) (height : 4 ≤ heightBase)
    (wordBound : wordWidth ≤ coeff*heightBase) :
    let bits:=RecordWidth (CheapISA.width wordWidth+1)
    let count:=TaggedWidthSlices.count (heightBase+bits) heightBase
    let width:=TaggedWidthSlices.width (heightBase+bits) heightBase
    0<count ∧ count ≤ 7*(coeff+6)+1 ∧ (∑ j,width j)=heightBase+bits ∧ ∀j,width j≤heightBase := by
  intro bits count width
  have fit : bits ≤ 7*(coeff+6)*heightBase := by
    change RecordWidth (wordWidth+5+1) ≤ 7*(coeff+6)*heightBase
    rw [recordWidth_eq,Nat.mul_assoc,Nat.add_mul]
    omega
  exact DescentTerminalChosenSort.fields bits (7*(coeff+6)) (by omega) fit

local notation "fields₀" => (physical_fields w h rate height wordBound)

-- The ordered stages and their field slices are fixed before the input assignment.
/-- The concrete sorter and header, applied to the original controller. -/
def physicalHost :=
  onProgram (D:=D) (P0:=P0) (L0:=L0) (positive:=positive) (C:=C) (Q:=Q)
    (n:=h) (s:=0) (stages:=schedule) (field:=slices)
    (cover:=(fields₀).2.2.1) (fitFields:=(fields₀).2.2.2)
    (widths:=widths) (Y:=Y₀) (hp:=hp) (hr:=hr) (st:=st) (initialRoom:=initialRoom)
    (time:=time) (ht:=ht) (short:=short) (width:=width) (init:=init)
    (seedCircuit:=seedCircuit) (original:=original) (table:=table)

local notation "realHost" => (physicalHost (D:=D) (P0:=P0) (L0:=L0) (positive:=positive) (C:=C) (Q:=Q)
  (widths:=widths) (hp:=hp) (hr:=hr) (st:=st) (initialRoom:=initialRoom) (time:=time)
  (ht:=ht) (short:=short) (width:=width) (init:=init) (seedCircuit:=seedCircuit)
  (original:=original) (table:=table) h rate height wordBound room Y₀)

/-- The real seven-level sort and fixed CPU charge one bit cost per original
program word, register, input word, observation and execution step. -/
theorem physical_price (payload : 0 < word) :
    hostSize realHost ≤
      4*(seedCircuit.cells+seedCircuit.internal)+9*(rows*word)+B*W+
      Fintype.card (Choice (A⊕Bits) rows word)+Fintype.card (Catalyst.Port dest widths)+
      (257*(1000*(2*scale+2)*(2*4^7+1))+256*fixedISAPrice*(rate+6))*
        (pcs+regs+S0+fuel+U+2^h+1)*(h+1) := by
  have span := (fixed_isa_sort_tariff labels height (ticket).1 (ticket).2.1 w rate wordBound).1
  have actual := priced (D:=D) (P0:=P0) (L0:=L0) (positive:=positive) (C:=C) (Q:=Q)
    (n:=h) (s:=0) (stages:=schedule) (field:=slices)
    (cover:=(fields₀).2.2.1) (fitFields:=(fields₀).2.2.2) (widths:=widths) (Y:=Y₀)
    (hp:=hp) (hr:=hr) (st:=st) (initialRoom:=initialRoom) (time:=time) (ht:=ht)
    (short:=short) (width:=width) (init:=init) (seedCircuit:=seedCircuit) (original:=original)
    (table:=table) payload (span.trans (Nat.mul_le_mul_left scale (Nat.le_succ _)))
    (DescentTerminalChosenSort.depth labels height (ticket).1 (ticket).2.1).le
  apply actual.trans
  have sorted := fixed_isa_source_sort labels h pcs regs S0 fuel U w rate height wordBound room
  have executed := fixed_isa_source_cost h pcs regs S0 fuel U w rate wordBound room
  let sortRate := 257*(1000*(2*scale+2)*(2*4^7+1))
  let cpuRate := 256*fixedISAPrice*(rate+6)
  let raw := pcs+regs+S0+fuel+U+2^h+1
  have both : (sortRate+cpuRate)*raw*(h+1) =
      sortRate*raw*(h+1)+cpuRate*raw*(h+1) := by ring
  have joined := Nat.add_le_add sorted executed
  change _ ≤ sortRate*raw*(h+1)+cpuRate*raw*(h+1) at joined
  rw [←both] at joined
  have addCharges {sorting processor budget : ℕ} (paid : sorting+processor ≤ budget)
      (fixed : ℕ) : fixed+sorting+processor ≤ fixed+budget :=
    (Nat.add_assoc fixed sorting processor).le.trans (Nat.add_le_add_left paid fixed)
  exact addCharges joined
    (4*(seedCircuit.cells+seedCircuit.internal)+9*(rows*word)+B*W+
      Fintype.card (Choice (A⊕Bits) rows word)+Fintype.card (Catalyst.Port dest widths))

set_option maxHeartbeats 800000 in
include chipRoom ready before in
/-- The same concretely priced host contracts to the weighted sum on its actual
external ports. All sort correctness, field widths and padding are supplied by
the chosen fixed network. -/
theorem physical_contraction (x : Catalyst.Port dest widths→ Bool) (outer : Ports bits)
    (base : Input→ℕ→ Word w)
    (root : ∀b i,Sum.elim (Sum.elim x b) id (init i)=TraceWords.bits (wide (base b i.1.val)) i.2)
    (m0 : Input→ Memory w) (earlier : ∀z,Q.Exec (initialMemory S0 (base z)) (m0 z) time)
    (cheap : CheapCode Q) (prior : Raw→(A→ Bool)→ Option T) (single : ∀x t,∃!z,prior x z=some t)
    (contents : T→ Raw→ Content K Cap q piece)
    (graph : T→ Network geo P bits) (tables : ∀t,(graph t).Tables F) (edges : ∀t,(graph t).Edge ↪ ℕ)
    (volume : ∀t,(∑e,(graph t).width e)≤ rows*word) (pos : 0< word) (posW : 0< W)
    (seedCount : T→ I→ℕ) (key : T→ Raw→ Fin slots→ Fin bins) (seedFit : ∀t i,seedCount t i<2^w)
    (countsFit : ∀t,Fintype.card (DescentTerminalSeedFactors.Occurs (seedCount t) (Fin slots))<2^W)
    (mounted : Current D P0 L0 prior contents (fun t=>∑e,(graph t).width e) seedCount key m0)
    (weight : T→ F) (factors : ∀z t pay,finalChoice dataRoom prior contents pay z=some t→
      TypedWiring.value seedCircuit (Sum.elim z pay)*
        ((∏i,original i^seedCount t i)*(∏j,table (key t pay j)))=weight t*∏v,(graph t).read (tables t)
        (takeBits (graph t) (denseBits (graph t) (edges t) (volume t)) pay) outer v) :
    exactValue _ realHost x=∑t,weight t*(graph t).value (tables t) outer := by
  let : Nonempty (Fin (TaggedWidthSlices.count (h+recordBits) h)) :=
    ⟨⟨0,(fields₀).1⟩⟩
  exact contraction (D:=D) (P0:=P0) (L0:=L0) (chipRoom:=chipRoom) (dataRoom:=dataRoom)
    (positive:=positive) (C:=C) (ready:=ready) (Q:=Q)
    (n:=h) (s:=0) (stages:=schedule) (field:=slices)
    (cover:=(fields₀).2.2.1) (fitFields:=(fields₀).2.2.2)
    (widths:=widths) (Y:=Y₀) (hp:=hp) (hr:=hr) (st:=st) (initialRoom:=initialRoom)
    (time:=time) (ht:=ht) (before:=before) (short:=short) (width:=width)
    (init:=init) (seedCircuit:=seedCircuit) (original:=original) (table:=table)
    (fun i b=>(DescentTerminalChosenSort.widths labels height (ticket).1 (ticket).2.1 i b).2)
    (DescentTerminalChosenSort.sorts labels height (ticket).1 (ticket).2.1)
    (ticket).2.2.1 x outer base root m0 earlier cheap prior single contents graph tables edges
    volume pos posW seedCount key seedFit countsFit mounted weight factors

end PhysicalSort


end
end Hierarchy.DescentTerminalFixedISAHost

end OAI
