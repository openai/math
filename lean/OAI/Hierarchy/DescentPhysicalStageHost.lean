import OAI.Hierarchy.DescentTerminalFixedISAHost
import OAI.Hierarchy.DescentTerminalChipPins
import OAI.Hierarchy.DescentTerminalSeedChip
import OAI.Hierarchy.DescentSeedInitialWorldCodes
import OAI.Hierarchy.DescentNativeInput
import OAI.Hierarchy.DescentEpochHistory

namespace OAI
/-! # The actual fixed-ISA host at the independent-copy coefficient boundary -/

namespace Hierarchy.DescentTerminalFixedISAHost
open DescentTerminalReadout DescentTerminalChipRuntime DescentTerminalChipPins
open ThreeFlat Routing SortNetwork Diagonal TraceRows TraceBanks
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory ProtocolRAM TaggedShorterControlHistory
open Catalyst CatalystSubstitution CorrectionBatch Tagged Tagged.SortLift TaggedShorterHistoryOrder
open DescentTerminalRAM DescentTerminalHost DescentTerminalPorts DescentTerminalThreshold DescentTerminalLast
open DescentCompiler DescentSixParty DescentInitialHost
open Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 1000000

attribute [local irreducible] DescentTerminalLast.program DescentTerminalLast.ticks
  DescentTerminalChipRuntime.program DescentTerminalChipRuntime.clocks
  Procedure.seq complete ProtocolRAM.machine CheapISA.machine

private abbrev installedProgram {J : Type} {w slots bins : ℕ} (D : Columns (I:=J))
    (layout : DescentTerminalChipRuntime.Layout) (banks : DescentTerminalChipRuntime.Banks)
    (census : DescentCensusRAM.Banks w slots bins) (prefixProgram : Procedure w)
    (pool cut stop rows word : ℕ) :=
  complete (D.tape layout pool) census (cut:=cut) (stop:=stop) (rows:=rows) (word:=word)
    (prefixProgram.seq (DescentTerminalChipRuntime.program layout banks w pool slots))

variable {F : Type} [Field F] {A I : Type} [Fintype A] [Fintype I]
    {arity pins groups radix R s Gheight dateDepth menu depthBound rounds : ℕ}
    (X : Approximation F arity pins) (G : PoweredGadget F)
    {u ε : ℝ} (hu : 0≤u) (he : 0≤ε)
    (digits : Fin R ≃ Fin groups × DescentColonies.Block radix)
local notation "origin" => SeedNamed.initial X R s groups radix digits
variable (epochPlan : Epochs G hu he (h:=dateDepth) (C:=menu) (Ht:=depthBound) (t:=rounds)
    Gheight (SeedNamed.initial X R s groups radix digits))
local notation "worlds" => Epochs.finish G hu he epochPlan
local notation "copies" => R*s
local notation "exterior" => Catalyst.Port (copies*pins) (CorrectionFrame.copiesWidth copies X.width)
variable {w S0 rows slots word bins W cut stop K Cap q piece : ℕ}
local notation "N" => K*Cap
local notation "Bits" => Inputs K Cap q piece
local notation "Raw" => RowBit rows word→Bool
local notation "Input" => Choice (A⊕Bits) rows word→Bool
variable (D : Columns (I:=I)) (P0 : DescentTerminalChipRuntime.Layout) (L0 : DescentTerminalChipRuntime.Banks)
    (chipRoom : Room P0 L0 w (K*Cap) slots) (dataRoom : q*(Cap*piece)≤w) (positive : 0<w)
local notation "L" => D.tape P0 N
variable (C : DescentCensusRAM.Banks w slots bins) (ready : Ready (D.tape P0 (K*Cap)) C cut stop rows word)
    (Q : Procedure w)
local notation "proc" => installedProgram D P0 L0 C Q (K*Cap) cut stop rows word
local notation "pcs" => (proc).labels+3
local notation "regs" => (proc).registers+1
local notation "B" => Fintype.card I+bins+1
local notation "U" => rows+B
variable (hp : (installedProgram D P0 L0 C Q (K*Cap) cut stop rows word).labels+3≤2^(w+1))
    (hr : (installedProgram D P0 L0 C Q (K*Cap) cut stop rows word).registers+1≤2^(w+1)) (st : Word w)
    (initialRoom : S0≤2^w) (time : ℕ)
local notation "fuel" => time+clocks N slots+ticks L C rows word+3
local notation "clock" => CheapISA.hostFuel fuel
variable (ht : CheapISA.hostFuel (time+clocks (K*Cap) slots+ticks (D.tape P0 (K*Cap)) C rows word+3)
      +(rows+(Fintype.card I+bins+1))≤2^(CheapISA.width w+1)) (before : ∀i,D.seed i<cut)
    (short : depth word≤w+1) (width : W≤w+1)
    (init : Fin S0×Fin (w+1) → (Catalyst.Port ((R*s)*pins) (CorrectionFrame.copiesWidth (R*s) X.width)⊕Choice (A⊕Inputs K Cap q piece) rows word)⊕Bool)
    (seedCircuit : BitNetwork F (Fintype.card (Choice (A⊕Inputs K Cap q piece) rows word)))
    (original : I→F) (table : Fin bins→F)
variable (h rate : ℕ) (height : 4≤h) (wordBound : w≤rate*h)
    (room : CheapISA.dataBase ((installedProgram D P0 L0 C Q (K*Cap) cut stop rows word).labels+3)
      ((installedProgram D P0 L0 C Q (K*Cap) cut stop rows word).registers+1)+S0+
      (CheapISA.hostFuel (time+clocks (K*Cap) slots+ticks (D.tape P0 (K*Cap)) C rows word+3)+
        (rows+(Fintype.card I+bins+1)))≤2^(3*h))
    (Y : Approximation F arity (Tagged.pins h h))
local notation "compiler" => physicalHost (D:=D) (P0:=P0) (L0:=L0) (positive:=positive) (C:=C) (Q:=Q)
  (widths:=CorrectionFrame.copiesWidth copies X.width) (hp:=hp) (hr:=hr) (st:=st) (initialRoom:=initialRoom) (time:=time)
  (ht:=ht) (short:=short) (width:=width) (init:=init) (seedCircuit:=seedCircuit)
  (original:=original) (table:=table) h rate height wordBound room Y
local notation "scale" => 7*(rate+6)

include chipRoom positive ready hp hr st initialRoom ht before short width height wordBound room

/-- On the concrete dated run, the same host gives all labelled coefficients and the
integral price used by oracle descent. Every seed and exterior assignment is read
through the real controller. The tagged calls come from its chosen sorting stages. -/
theorem physical_stage_host_dependent (base : (exterior→Bool) → Input → ℕ → Word w)
    (root : ∀x b i,Sum.elim (Sum.elim x b) id (init i)=TraceWords.bits (wide (base x b i.1.val)) i.2)
    (m0 : (exterior→Bool) → Input → Memory w)
    (earlier : ∀x z,Q.Exec (initialMemory S0 (base x z)) (m0 x z) time)
    (cheap : CheapCode Q)
    (prior : (exterior→Bool) → Raw → (A→Bool) → Option (worlds).Choice) (single : ∀x pay t,∃!z,prior x pay z=some t)
    (contents : (exterior→Bool) → (worlds).Choice → Raw → Content K Cap q piece)
    (edges : ∀t,((worlds).state t).graph.Edge ↪ ℕ)
    (volume : ∀t,(∑e,((worlds).state t).graph.width e)≤rows*word) (pos : 0<word) (posW : 0<W)
    (seedCount : (worlds).Choice→I→ℕ) (key : (exterior→Bool) → (worlds).Choice→Raw→Fin slots→Fin bins)
    (seedFit : ∀t i,seedCount t i<2^w)
    (countsFit : ∀t,Fintype.card (DescentTerminalSeedFactors.Occurs (seedCount t) (Fin slots))<2^W)
    (mounted : ∀x,Current D P0 L0 (prior x) (contents x) (fun t=>∑e,((worlds).state t).graph.width e)
      seedCount (key x) (m0 x))
    (factors : ∀(x : exterior→Bool) z t pay,finalChoice dataRoom (prior x) (contents x) pay z=some t →
      TypedWiring.value seedCircuit (Sum.elim z pay)*
        ((∏i,original i^seedCount t i)*(∏j,table (key x t pay j)))=
      (worlds).weight t*∏v,((worlds).state t).graph.read ((worlds).state t).tables
        (takeBits ((worlds).state t).graph (denseBits _ (edges t) (volume t)) pay) (packagePins X R s x) v)
    (M J cost : ℕ)
    (paid : (4*(seedCircuit.cells+seedCircuit.internal)+9*(rows*word)+B*W+
      Fintype.card (Choice (A⊕Bits) rows word)+Fintype.card exterior+
      (257*(1000*(2*scale+2)*(2*4^7+1))+256*fixedISAPrice*(rate+6))*
        (pcs+regs+S0+fuel+U+2^h+1)*(h+1))*2^J≤cost*copies*(M+2^J*Fintype.card (Port pins X.width))) :
    ∃ calls : ℕ, ∃ H : Host F arity (copies*pins) (Sockets (List.replicate calls (CollapseOracle.tagCall h Y))),
      Agrees (independentCopies copies X) (tableApprox H.width (exactValue _ H)) ∧
        hostSize H*2^J≤cost*copies*(M+2^J*Fintype.card (Port pins X.width)) := by
  refine ⟨_,compiler,⟨rfl,?_⟩,?_⟩
  · intro x
    have eval:=physical_contraction (D:=D) (P0:=P0) (L0:=L0) (chipRoom:=chipRoom)
      (dataRoom:=dataRoom) (positive:=positive) (C:=C) (ready:=ready) (Q:=Q) (widths:=CorrectionFrame.copiesWidth copies X.width)
      (hp:=hp) (hr:=hr) (st:=st) (initialRoom:=initialRoom) (time:=time) (ht:=ht)
      (before:=before) (short:=short) (width:=width) (init:=init)
      (seedCircuit:=seedCircuit) (original:=original) (table:=table) h rate height wordBound room Y
      x (packagePins X R s x) (base x) (root x) (m0 x) (earlier x) cheap (prior x) (single x) (contents x)
      (fun t=>((worlds).state t).graph) (fun t=>((worlds).state t).tables) edges volume pos posW
      seedCount (key x) seedFit countsFit (mounted x) (worlds).weight (factors x)
    have terminal : exactValue _ compiler x=(worlds).value (packagePins X R s x) := eval
    have coefficient : (independentCopies copies X).coeff x = exactValue _ compiler x :=
      ((terminal.trans (Epochs.value G hu he origin epochPlan _)).trans
        ((congrFun (SeedNamed.initial_value X R s groups radix digits) _).trans
          (complete_input X R s x))).symm
    exact coefficient.trans (tableApprox_coeff (compiler).width (exactValue _ compiler) x).symm
  · exact (Nat.mul_le_mul_right (2^J) (physical_price (D:=D) (P0:=P0) (L0:=L0) (positive:=positive)
      (C:=C) (Q:=Q) (widths:=CorrectionFrame.copiesWidth copies X.width) (hp:=hp) (hr:=hr) (st:=st) (initialRoom:=initialRoom) (time:=time)
      (ht:=ht) (short:=short) (width:=width) (init:=init) (seedCircuit:=seedCircuit)
      (original:=original) (table:=table) h rate height wordBound room Y pos)).trans paid

theorem physical_stage_host (base : (exterior→Bool) → Input → ℕ → Word w)
    (root : ∀x b i,Sum.elim (Sum.elim x b) id (init i)=TraceWords.bits (wide (base x b i.1.val)) i.2)
    (m0 : (exterior→Bool) → Input → Memory w)
    (earlier : ∀x z,Q.Exec (initialMemory S0 (base x z)) (m0 x z) time)
    (cheap : CheapCode Q)
    (prior : Raw → (A→Bool) → Option (worlds).Choice) (single : ∀x t,∃!z,prior x z=some t)
    (contents : (worlds).Choice → Raw → Content K Cap q piece)
    (edges : ∀t,((worlds).state t).graph.Edge ↪ ℕ)
    (volume : ∀t,(∑e,((worlds).state t).graph.width e)≤rows*word) (pos : 0<word) (posW : 0<W)
    (seedCount : (worlds).Choice→I→ℕ) (key : (worlds).Choice→Raw→Fin slots→Fin bins)
    (seedFit : ∀t i,seedCount t i<2^w)
    (countsFit : ∀t,Fintype.card (DescentTerminalSeedFactors.Occurs (seedCount t) (Fin slots))<2^W)
    (mounted : ∀x,Current D P0 L0 prior contents (fun t=>∑e,((worlds).state t).graph.width e)
      seedCount key (m0 x))
    (factors : ∀(x : exterior→Bool) z t pay,finalChoice dataRoom prior contents pay z=some t →
      TypedWiring.value seedCircuit (Sum.elim z pay)*
        ((∏i,original i^seedCount t i)*(∏j,table (key t pay j)))=
      (worlds).weight t*∏v,((worlds).state t).graph.read ((worlds).state t).tables
        (takeBits ((worlds).state t).graph (denseBits _ (edges t) (volume t)) pay) (packagePins X R s x) v)
    (M J cost : ℕ)
    (paid : (4*(seedCircuit.cells+seedCircuit.internal)+9*(rows*word)+B*W+
      Fintype.card (Choice (A⊕Bits) rows word)+Fintype.card exterior+
      (257*(1000*(2*scale+2)*(2*4^7+1))+256*fixedISAPrice*(rate+6))*
        (pcs+regs+S0+fuel+U+2^h+1)*(h+1))*2^J≤cost*copies*(M+2^J*Fintype.card (Port pins X.width))) :
    ∃ calls : ℕ, ∃ H : Host F arity (copies*pins) (Sockets (List.replicate calls (CollapseOracle.tagCall h Y))),
      Agrees (independentCopies copies X) (tableApprox H.width (exactValue _ H)) ∧
        hostSize H*2^J≤cost*copies*(M+2^J*Fintype.card (Port pins X.width)) := by
  exact physical_stage_host_dependent X G hu he digits epochPlan D P0 L0 chipRoom dataRoom positive C ready Q hp hr st
    initialRoom time ht before short width init seedCircuit original table h rate height wordBound room Y
    base root m0 earlier cheap (fun _=>prior) (fun _=>single) (fun _=>contents) edges volume pos posW
    seedCount (fun _=>key) seedFit countsFit mounted factors M J cost paid

attribute [deprecated_arg run epochPlan (since := "2026-11-16")]
  physical_stage_host_dependent physical_stage_host

end
end Hierarchy.DescentTerminalFixedISAHost

end OAI
