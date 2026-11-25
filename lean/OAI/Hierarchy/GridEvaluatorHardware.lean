import OAI.Hierarchy.GridNativeImage
import OAI.Hierarchy.GridRegisteredPublication
import OAI.Hierarchy.TraceResourceHardware
import OAI.Hierarchy.GridPhysicalAdmission
import OAI.ThreeFlat.Diagonal.InitialMetadataCost
import OAI.ThreeFlat.Diagonal.NavigationRepeatedSize

namespace OAI
/-! # Hardware of the installed original-grid evaluator

The three size parameters are bounded together before the approximation or
selector is chosen. The repeated block and its initial signed degree determine
the only non-universal pieces of the instruction count. -/
namespace Hierarchy.GridEvaluatorHardware
open ThreeFlat RAM PhysicalProcedure Diagonal PhysicalStage
open NavigationPass NavigationDirectory NodePublication Computability.VPVNP.BurstRAM PrivateRAM Filter
open TraceNodeHeaders
open scoped Classical Fin.CommRing Topology
open HistoryStageBody.Physical (resources resources_seq resources_scan)
open TraceAdmission GridRegisteredSetting
noncomputable section

/-- All three bit streams are loaded by counted scans. The metadata pass
contains one compiled term for each of the two halves of each initial port. -/
theorem seed_size {W : ℕ} (a : Archive) (ss : List Stage) (edges n : ℕ) :
    resources (TraceSeedWriter.procedure (W:=W) a ss edges n) = 4465+2192*a.initialDegree := by
  let C : SlotImage.Columns := ⟨a.cursor.graph,a.axes*a.initialDegree,a.cursor.width⟩
  let boot := InitialRelayBootstrap.procedure (a.control : Word W) C a.axes a.initialDegree a.relayWidth
  obtain ⟨lb,rb,sb⟩ := InitialRelayBootstrap.size (a.control : Word W) C a.axes a.initialDegree a.relayWidth
  have relay : resources boot=708 := by change boot.labels+boot.registers+boot.slots=_; dsimp only [boot]; omega
  have loads : resources (a.boot (W:=W) ss edges)=89 := rfl
  have metadata : resources (a.initialMetadata (W:=W))=3658+2192*a.initialDegree := by
    simp only [Archive.initialMetadata,resources_seq,resources_scan,HeaderScan.binds_closed,
      Archive.initialKernel_work,Archive.initialHalfHeader_work,Archive.initialHalf_work]
    omega
  simp only [TraceSeedWriter.procedure,resources_seq,loads,metadata]
  change 89+(resources boot+((3658+2192*a.initialDegree)+(5+5)))=_
  omega

/-- The six publisher loops use fixed row opcodes. The 376-bind expression
for the immutable header contributes its actual compiled register and PC counts. -/
theorem pin_size (W rails : ℕ) (P : GridPinPublisher.Plan) :
    resources (P.canonicalProgram W rails) ≤ 2000 := by
  let e : DescriptorExpr.Term W 0 1 := HeaderScan.closed (GridPinHeaderNative.headerExpr W P.header)
  have work : e.binds=376 := (HeaderScan.binds_closed _).trans (GridPinHeaderNative.header_work ..)
  have code : e.labels=3*e.binds+1 := e.labels_eq
  have header : resources (GridPinHeaderNative.procedure W P.ticks P.header)=1515 := by
    change (6+e.labels)+(4+e.binds)+0=_; omega
  simp only [GridPinPublisher.canonicalProgram,GridPinPublisher.program,resources_seq,header]
  simp only [resources,FactorBucketRAM.procedure]; decide

/-- Threshold loading and all four passes of the factor allocator. -/
theorem assignment_size (w src roots dir T : ℕ) :
    resources (GridSimulation.assign w src roots dir T) ≤ 250 := by
  simp only [GridSimulation.assign, FactorBucketRAM.compiler, resources_seq]
  simp only [resources, TraceAdmission.inputPacker, FactorBucketRAM.procedure]; decide

/-- Complete physical resource publication, including both ordered rail and data banks. -/
theorem publication_size (w m n B q d np ell text S roots stages full span logRadix pc : ℕ) :
    resources (GridRegisteredPublication.procedure w m n B q d np ell text S roots stages full span logRadix pc) ≤ 5291 := by
  let rails := GridControllerSimGeometry.railCount m n B
  let P := GridPinPublisher.canonical w (m+1) n q d np ell text B rails S roots stages full (2*span)
  let A := GridCompilerAdmission.arena w
  let b := GridControllerIdle.shape m n B logRadix q d pc
  let src := GridSimulation.thresholdSource w rails B np
  let T := (n+1)^(m+1)*q
  have classCost := assignment_size w src roots ((m+1)+2) T
  have pinCost := pin_size (64*w) rails P
  have geo := GridControllerSimGeometry.receiver_text (64*w) A b (A.data rails n)
  change resources (((GridSimulation.assign w src roots ((m+1)+2) T).seq (P.canonicalProgram (64*w) rails)).seq
    ((GridControllerSimGeometry.program (64*w) A b).seq (GridOrderedDataRAM.prepare (64*w) (A.data rails n) b.data (b.rails*2)))) ≤ _
  rw [resources_seq,resources_seq]
  change resources ((GridControllerSimGeometry.program (64*w) A b).seq
    (GridOrderedDataRAM.prepare (64*w) (A.data rails n) b.data (b.rails*2))) ≤ 3041 at geo
  omega

/-- Bound the actual emitter after the architecture of its expander block has been chosen. -/
theorem emit_size {F : Type} [Field F] [Fintype F] (block : Block F) : ∃ H, ∀
    (w axes off slots cap static blocks : ℕ) (ss : List Stage) (edges : ℕ)
    (lanes per pairs trace tariff header dp directory steps dst : ℕ)
    (layer : NavigationNodeRows.Layer) (p : Resources.Parameters ℕ)
    (m n B q d np text S roots full span logRadix pc fieldSize pRaw limit : ℕ) (zero one : Word (64*w)),
    let a := TraceSeedWriter.archive block w axes off slots cap static
    let num := directoryCap block
    let node := traceArchive w lanes per pairs trace tariff num num num
    let admission := GridPhysicalAdmission.program block a ss edges (64*w) blocks
    let registration := Resources.registerNodes (64*w) (compactControl w) header dp directory steps dst node layer p
    let publication := GridRegisteredPublication.procedure w m n B q d np (cap+1) text S roots steps full span logRadix pc
    let ar := GridCompilerAdmission.arena w
    let b := GridControllerIdle.shape m n B logRadix q d pc
    let idle := GridControllerIdle.guarded (64*w) ar b cap
    let sim := admission.seq (registration.seq publication)
    let dispatch := GridSelectorSwitch.program (12*ar.J : ℕ) idle sim
    let e := GridControllerSimGeometry.railCount m n B
    let emit := GridCompilerAdmission.emit dispatch B n (m+1) pRaw e limit fieldSize zero one
    resources emit+59 ≤ H := by
  obtain ⟨R,repeatBound⟩ := repeated_hardware block block.alphabetCap
  let U := 2^(block.exponent 0)
  let V := 100+compactHardware (directoryCap block)+Resources.registerSize
  refine ⟨R+2192*U+V+130000,?_⟩
  intro w axes off slots cap static blocks ss edges lanes per pairs trace tariff header dp directory steps dst
    layer p m n B q d np text S roots full span logRadix pc fieldSize pRaw limit zero one
    a num node admission registration publication ar b idle sim dispatch e emit
  have seed := seed_size (W:=64*w) a ss edges blocks
  have fold := repeatBound (64*w) (a.control : Word (64*w)) ((a.control+1:ℕ) : Word (64*w))
  have last := GridSelector.terminal_hardware a ss edges (64*w)
  change resources (TerminalWireArchive.program (W:=64*w) (a.terminal ss edges (64*w))) ≤ 2000 at last
  have adm : resources admission ≤ (4465+2192*U)+R+2000 := by
    dsimp only [admission,GridPhysicalAdmission.program]
    rw [resources_seq,resources_seq,seed]
    change (4465+2192*U)+(resources (NavigationPass.repeated (a.control : Word (64*w)) ((a.control+1:ℕ) : Word (64*w)) block.alphabetCap block)+_) ≤ _
    omega
  have regCost : resources registration=V := Resources.native_registration_hardware w lanes per pairs trace tariff
    (directoryCap block) header dp directory steps dst layer p
  have pubCost := publication_size w m n B q d np (cap+1) text S roots steps full span logRadix pc
  change resources publication ≤ 5291 at pubCost
  have simCost : resources sim=resources admission+resources registration+resources publication := by
    dsimp only [sim]; rw [resources_seq,resources_seq]; omega
  have idleCost := GridControllerIdle.guarded_text_bound (64*w) ar b cap
  change resources idle ≤ 12000 at idleCost
  have switchCost : resources dispatch=6+resources idle+resources sim := by
    change (4+(idle.labels+sim.labels))+(2+(idle.registers+sim.registers))+(idle.slots+sim.slots)=_
    unfold resources; omega
  have machine := GridCompilerAdmission.hardware dispatch B n (m+1) pRaw e limit fieldSize zero one
  change resources emit ≤ resources dispatch+100027 at machine
  omega

/-- This is exactly room for the program, registers and immutable operands of
`GridNativeEvaluator.machine emit stage selector evalData`. -/
theorem capacity_of_price {w : ℕ} (emit : Procedure (64*w)) {H : ℕ}
    (hardware : resources emit+59 ≤ H) (mature : H ≤ GridDescription.capacity w) :
    (9+emit.labels)+35 ≤ GridDescription.capacity w ∧
      emit.registers+10 ≤ GridDescription.capacity w ∧ emit.slots+5 ≤ GridDescription.capacity w := by
  unfold resources at hardware; omega

/-- Room in the actual PC, register and public operand types at every mature word width. -/
theorem eventually_machine {F : Type} [Field F] [Fintype F] (block : Block F) : ∀ᶠ w : ℕ in atTop, ∀
    (axes off slots cap static blocks : ℕ) (ss : List Stage) (edges : ℕ)
    (lanes per pairs trace tariff header dp directory steps dst : ℕ)
    (layer : NavigationNodeRows.Layer) (p : Resources.Parameters ℕ)
    (m n B q d np text S roots full span logRadix pc fieldSize pRaw limit : ℕ) (zero one : Word (64*w)),
    let a := TraceSeedWriter.archive block w axes off slots cap static
    let num := directoryCap block
    let node := traceArchive w lanes per pairs trace tariff num num num
    let admission := GridPhysicalAdmission.program block a ss edges (64*w) blocks
    let registration := Resources.registerNodes (64*w) (compactControl w) header dp directory steps dst node layer p
    let publication := GridRegisteredPublication.procedure w m n B q d np (cap+1) text S roots steps full span logRadix pc
    let ar := GridCompilerAdmission.arena w
    let b := GridControllerIdle.shape m n B logRadix q d pc
    let idle := GridControllerIdle.guarded (64*w) ar b cap
    let sim := admission.seq (registration.seq publication)
    let dispatch := GridSelectorSwitch.program (12*ar.J : ℕ) idle sim
    let e := GridControllerSimGeometry.railCount m n B
    let emit := GridCompilerAdmission.emit dispatch B n (m+1) pRaw e limit fieldSize zero one
    (9+emit.labels)+35 ≤ GridDescription.capacity w ∧ emit.registers+10 ≤ GridDescription.capacity w ∧
      emit.slots+5 ≤ GridDescription.capacity w := by
  obtain ⟨H,all⟩ := emit_size block
  filter_upwards [GridDescription.eventually_fits H H H] with w room
  intro axes off slots cap static blocks ss edges lanes per pairs trace tariff header dp directory steps dst
    layer p m n B q d np text S roots full span logRadix pc fieldSize pRaw limit zero one
    a num node admission registration publication ar b idle sim dispatch e emit
  exact capacity_of_price emit (all w axes off slots cap static blocks ss edges lanes per pairs trace tariff
    header dp directory steps dst layer p m n B q d np text S roots full span logRadix pc fieldSize pRaw limit zero one) room.1

/-- All three actual hardware indices of a machine fit the description's chosen architecture. -/
def FitsCapacity {w p r k : ℕ} (_ : Machine (64*w) p r k) :=
  p ≤ GridDescription.capacity w ∧ r ≤ GridDescription.capacity w ∧ k ≤ GridDescription.capacity w

set_option maxHeartbeats 1000000 in
/-- The uniform result on the exact executable installed before diagonal self-substitution. -/
theorem installed {F : Type} [Field F] [Fintype F] (block : Block F) : ∀ᶠ w : ℕ in atTop,
    ∀ {pc regs slots S base fuel axes : ℕ}
      (D : RunData F (64*w) pc regs slots S base fuel axes (w/2)) (l : GridNativeImage.Layout),
      D.block=block → ∀ X : Catalyst.Approximation F (l.dimension+1) (l.copies*l.pinWidth),
        FitsCapacity (w:=w) (p:=(9+(GridNativeImage.emitter D l).labels)+35)
          (r:=(GridNativeImage.emitter D l).registers+10) (k:=(GridNativeImage.emitter D l).slots+5)
          (GridNativeImage.machine D l X) := by
  filter_upwards [eventually_machine block] with w hardware
  intro pc regs slots S base fuel axes D l isBlock X
  subst block
  let depth := (axes+1)+w/2
  let grid := TraceStaticRow.gateTable D.field D.fit.width D.fit.labels base fuel D.state regs slots depth
  let off := 1+(depth+depth)
  let desc := TraceSourceOwner.shape (64*w) pc regs slots S fuel depth grid.internal
  let trace := TraceBitHeader.seedTraceWork (w/2) desc.stride grid.cells D.block.cursorCopies depth
  let P := D.block.repeat D.passes
  let rem := axes+1-P.charge
  let ss := P.directory rem (axes+1)
  let edges := P.finalEdges rem (axes+1)
  let a := GridNativeImage.archive D l
  let last := TraceRecovery.lastLayer a.K ss a.cursor a.seedLayer
  let e := GridControllerSimGeometry.railCount l.dimension l.sideMinusOne l.bank
  change (9+(GridNativeImage.emitter D l).labels)+35 ≤ GridDescription.capacity w ∧
    (GridNativeImage.emitter D l).registers+10 ≤ GridDescription.capacity w ∧
    (GridNativeImage.emitter D l).slots+5 ≤ GridDescription.capacity w
  dsimp only [GridNativeImage.emitter, GridNativeImage.dispatch, GridNativeImage.simulated, GridNativeImage.node]
  exact hardware (axes+1) off grid.cells l.selectorCap (e*2+w^2+l.bank*w^2) D.passes ss edges
    (2^(axes+1)) (2^(w/2)) ((S+1)/2) trace (D.issuedUnit w l.degree l.stageRate l.rootRate)
    (a.control+64) (traceLimit w) a.cursor.header ss.length (14*GridDescription.sector w)
    a.seedLayer (GridNativeImage.resources D l) l.dimension l.sideMinusOne l.bank l.copies l.pinWidth
    (GridNativeImage.parameterCount D l) l.receiverText S last.count (2^(axes+1)) (2^(w/2)) l.logRadix
    l.receiverPC (Fintype.card F) (l.copies*l.pinWidth) (GridNativeImage.limit F l)
    ((FieldCode.ofCardLe D.field).encode 0) ((FieldCode.ofCardLe D.field).encode 1)

/-- Clock at the same installed image. The published header count is taken from
its real compiled-PC and grid descriptors and includes both directory copies. -/
theorem installed_clock {F : Type} [Field F] [Fintype F] {Q : ℕ → ℕ} {E : ℕ → ℝ}
    (env : GridScale.Envelopes Q E) (block : Block F) {u s : ℕ → ℕ}
    (scale : TraceDistribution.Scale u s) (m A : ℕ) : ∀ᶠ w : ℕ in atTop, ∀ q, 0 < q → q ≤ Q w →
    let a := GridScale.overhead Q E w
    let bank := GridScale.pairs A w q
    let pin := GridScale.pins w a
    let ell := GridScale.selector (m+1) w a
    ∀ {pc regs slots S base fuel axes : ℕ} (D : RunData F (64*w) pc regs slots S base fuel axes (w/2)),
      D.block=block → D.passes=s w → axes+1=u w+1-w/2 →
      pc ≤ 64*w → regs ≤ 64*w → slots ≤ 64*w →
      ∀ n receiverText receiverPC logRadix degree stageRate rootRate, n+1=GridScale.side a →
        let l : GridNativeImage.Layout := ⟨m,n,bank,q,pin,ell-1,receiverText,receiverPC,logRadix,degree,stageRate,rootRate⟩
        let rails := GridControllerSimGeometry.railCount m n bank
        S=GridSelfHeader.rawSize w rails bank (GridNativeImage.parameterCount D l) →
        ∀ X : Catalyst.Approximation F (m+1) (q*pin), X.size ≤ bank →
          (GridNativeEvaluator.tailTime (n:=n) (e:=rails) X+GridNativeImage.emissionTime D l)+4+5*ell ≤
            GridScale.evalWork w (m+1) A 2 a q := by
  let C := GridStructuralHeader.coefficient block
  have ur := (tendsto_order.mp scale.cap).2 2 (by norm_num)
  have sr := (tendsto_order.mp scale.blocks).2 1 (by norm_num)
  filter_upwards [GridEvaluatorBudget.eventual_execution env block scale m A C 14,ur,sr,
    eventually_ge_atTop (Fintype.card F+1)] with w time uNear sNear large
  intro q hq top a bank pin ell pc regs slots S base fuel axes D same passes axis hp hr hs
    n receiverText receiverPC logRadix degree stageRate rootRate hn l rails input X size
  subst block
  have wpos : 0 < w := by omega
  have realPos : (0:ℝ) < w := by exact_mod_cast wpos
  have uBound : u w ≤ 2*w := by exact_mod_cast ((div_lt_iff₀ realPos).mp uNear).le
  have sBound : s w ≤ w := by exact_mod_cast (by simpa using ((div_lt_iff₀ realPos).mp sNear).le : (s w:ℝ) ≤ w)
  let depth := axes+1+w/2
  let grid := TraceStaticRow.gateTable D.field D.fit.width D.fit.labels base fuel D.state regs slots depth
  let off := 1+(depth+depth)
  have np : GridNativeImage.parameterCount D l ≤ C*(w+1)^14 :=
    GridStructuralHeader.parameter_count D.block (axes+1) D.passes (ell-1) D.machine D.fit D.field D.state
      (by rw [passes];exact sBound) (by omega) hp hr hs (by omega)
  have fits : D.block.blockCharge*s w ≤ u w+1-w/2 := by rw [← axis,← passes];exact D.passesFit
  have railEq : GridScale.external (m+1) a bank=rails := by
    change (m+1)*(2*(GridScale.side a)^((m+1)-1)*bank)=(m+1)*(2*(n+1)^m*bank)
    rw [← hn]; simp only [Nat.add_sub_cancel]
  have result := time q hq top fits n (GridNativeImage.parameterCount D l) receiverText off grid.cells
    (rails*2+w^2+bank*w^2) logRadix receiverPC (GridCompilerAdmission.arena w) X hn np size
  rw [railEq,← input,← axis,← passes] at result
  exact result

end
end Hierarchy.GridEvaluatorHardware

end OAI
