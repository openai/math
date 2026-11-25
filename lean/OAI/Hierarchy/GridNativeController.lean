import OAI.Hierarchy.GridAdmissionContinuation
import OAI.Hierarchy.GridPhysicalEmission
import OAI.Hierarchy.GridRegisteredIssuedRoom

namespace OAI
/-! # The native computation from a selected input to the grid controller's pin banks -/

noncomputable section
namespace Hierarchy.GridNativeController
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows RAM.PhysicalProcedure RAM.TickStageSpec Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution TraceAdmission TraceNodeHeaders NodePublication GridRegisteredSetting Filter
open scoped Classical Topology Fin.CommRing

variable {F : Type} [Field F] [Fintype F]

private theorem load_twice {W k p : ℕ} (X : Catalyst.Approximation F k p) (enc : FieldCode F W)
    (bank addr : ℕ) (mem : Memory W) :
    GridApproximationAdvice.paddedMemory X enc bank addr
      (GridApproximationAdvice.paddedMemory X enc bank addr mem)=GridApproximationAdvice.paddedMemory X enc bank addr mem := by
  funext i
  by_cases h : addr ≤ i ∧ i<addr+12*bank <;> simp [GridApproximationAdvice.paddedMemory,fillSegment,h]

variable (blk : Block F)

/-- The selected branch of the evaluator. Both the program and its time
bound are independent of the input bits, the selector and its decoded
history. The postcondition is the actual compact-X, passage and pin image
of the setting selected from the complete true trace. -/
theorem simulate {u s : ℕ → ℕ} (scale : Scale u s) (coef exp : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ {pc regs words k S base fuel : ℕ} (hk : 2 ≤ k+1)
      (axis : k+1=u w+1-w/2) (hp : pc ≤ 64*w) (hr : regs ≤ 64*w) (hs : words ≤ 64*w)
      (machine : Machine (64*w) pc regs words) (fit : NativeTrace.Fits machine S base ((k+1)+w/2) fuel)
      (hF : Fintype.card F ≤ 2^(64*w)) (state : Word (64*w)) (reps : blk.blockCharge*s w ≤ k+1)
      {m n B q d cap text tp tr tk logRadix : ℕ}
      (cat : Catalyst.Approximation F (m+1) (q*d)) (reserved : ∀ j,cat.width j ≤ B)
      (recv : Machine (64*w) tp tr tk) (raw gateBase : ℕ)
      (pins : Fin (GridControllerSimGeometry.railCount m n B*2) → Bool) (sel : Fin (cap+1) → Bool)
      (textFit : text ≤ w^2) (axisFit : m+1 ≤ w) (cutFit : 2^(3*w/5) ≤ cap)
      (dep setup maps : ℕ) (depFit : dep ≤ coef*(w+1)^exp)
      (setupFit : setup ≤ coef*(w+1)^exp) (mapFit : maps ≤ coef*(w+1)^exp),
      let W := 64*w
      let J := GridDescription.sector w
      let rails := GridControllerSimGeometry.railCount m n B
      let full := 2^(k+1)
      let span := 2^(w/2)
      let depth := (k+1)+w/2
      let grid := TraceStaticRow.gateTable hF fit.width fit.labels base fuel state regs words depth
      let off := 1+(depth+depth)
      let static := rails*2+w^2+B*w^2
      let a := TraceSeedWriter.archive blk w (k+1) off grid.cells cap static
      let P := blk.repeat (s w)
      let rem := k+1-P.charge
      let split : k+1=P.charge+rem := by dsimp only [P,rem]; rw [blk.charge_repeat]; omega
      let X := blk.cursorState hk (w/2) off grid.cells
      let _Y : State (2^blk.exponent 0) (P.charge+rem) := split ▸ X
      let ss := P.directory rem (k+1)
      let last := TraceRecovery.lastLayer a.K ss a.cursor a.seedLayer
      let D : RunData F W pc regs words S base fuel k (w/2) := ⟨machine,fit,hF,state,blk,hk,s w,reps⟩
      let C := (Physical.registerOnLanes blk (Fin S→Bool) (s w) rem X split).2
      let O := a.cursorSeedSites blk hk (w/2) off grid.cells rfl rfl
      let desc := TraceSourceOwner.shape W pc regs words S fuel depth grid.internal
      let trace := TraceBitHeader.seedTraceWork (w/2) desc.stride grid.cells blk.cursorCopies depth
      let unit := FactorWork.archiveTariff w dep setup maps P.length blk.localCoefficient
      let node := traceArchive w full span ((S+1)/2) trace unit (directoryCap blk) (directoryCap blk) (directoryCap blk)
      let band := GridIdleLayout.each m n B
      let p := Resources.gridRows w full last.count (m+1) span band S node.banks.charges last.first
      let enc := FieldCode.ofCardLe hF
      let params := GridStructuralHeader.parameters blk (k+1) (s w) cap machine fit hF state raw gateBase
      let np := GridStructuralHeader.wordCount (GridStructuralHeader.directory (w:=w) blk (k+1) (s w) cap).length
        (TraceReceiverTemplate.count grid) (HistoryStageBody.Physical.libraryWords blk (64*w))
      let capture := GridPinPublisher.capture (compact:=B) cat enc params recv machine pins sel
      let initial := GridApproximationAdvice.paddedMemory cat enc B (2*J) capture
      let _source := GridStructuralHeader.selectorBit cap sel
      let header := GridRegisteredPublication.headers (m:=m) (n:=n) (q:=q) D params recv sel textFit
      let advice := GridPinCapturedSources.advice (S:=S) (e:=rails) (compact:=B) cat enc params recv machine
      let arena := GridCompilerAdmission.arena w
      let arch := GridControllerIdle.shape m n B logRadix q d tp
      let rows := Resources.registerNodes W (compactControl w) (a.control+64) (traceLimit w) a.cursor.header
        ss.length (14*J) node O.layer p
      let writer := GridRegisteredPublication.procedure w m n B q d np (cap+1) text S last.count
        ss.length full span logRadix tp
      let time := GridRegisteredPublication.clock w m n B q d np (cap+1) text S last.count
        ss.length full span logRadix tp
      let edges := P.finalEdges rem (k+1)
      let readProc := GridPhysicalAdmission.program blk a ss edges W (s w)
      GridSelfHeader.rawSize w rails B np≤J → 12*B≤J → cap≤J → 0<q*d →
      GridSelfHeader.rawSize w rails B np≤S →
      GridPinArena.Small w (GridPinPublisher.canonical w (m+1) n q d np (cap+1) text B rails S last.count
        ss.length full (2*span)) S full (ss.length*full) ((20*(w+1)+2)^((m+1)+2)) →
      GridControllerIdle.Fits W arena arch → GridControllerIdle.Room arena arch →
      GridOrderedSources.Fits (r:=rails) (n:=n) (w:=W) cat arena B →
      ∃ enough : blk.repeatFactor*(X.maxWidth+1)*blk.widthBase^(s w)<2^W,
        let table:=physicalTable blk hk (w/2) off grid.cells (s w) W reps enough
        let read:=GridSelector.read D.run.plan table.codes (GridPhysicalSelector.bits D.run) cap
          (List.ofFn (Fin.tail sel))
        ∀ rooms : ∀ z : D.trace,D.Room z.1 C unit w m n B q d header, sel 0=true →
          Admission enc (readProc.seq (rows.seq writer)).block (readProc.seq (rows.seq writer)).publicData
            (·=initial) (fun _=>read.isSome) (fun _ out=>∀ z,read=some z→GridOrderedSources.Raw cat
              (D.scheduled p z.1 C unit header advice (rooms z) cat reserved).1 enc arena B pins out initial)
            ((2^(3*w/5)+(2^(3*w/5)+Archive.terminalTime (a.terminal ss edges W)))+(2*2^(3*w/5)+time)) := by
  filter_upwards [GridPhysicalAdmission.admits blk scale,GridPhysicalEmission.post_raw blk scale coef exp]
    with w validated issued
  intro pc regs words k S base fuel hk axis hp hr hs machine fit hF state reps m n B q d cap text tp tr tk logRadix
    cat reserved recv raw gateBase pins sel textFit axisFit cutFit dep setup maps depFit setupFit mapFit
    W J rails full span depth grid off static a P rem split X ss last D C O desc trace unit node band p enc
    params np capture initial header advice arena arch rows writer time edges readProc
    rawSpace compact capFit pos rawSize small fitIdle roomIdle fitsWriter
  let _Y : State (2^blk.exponent 0) (P.charge+rem) := split ▸ X
  let _source := GridStructuralHeader.selectorBit cap sel
  obtain ⟨enough,admitted⟩:=validated hk axis hp hr hs machine fit hF state reps cat recv raw gateBase pins sel
    rawSpace compact capFit cutFit
  refine ⟨enough,?_⟩
  intro table read rooms flag
  let inner:=blk.recordTable blk.alphabetCap W (s w) rem _Y le_rfl
    (by rw [State.maxWidth_cast_lanes,←Nat.mul_assoc];exact enough)
  let origin:=TraceSeedWriter.memory a ss edges [] _source initial (s w)
  apply follow_read enc readProc (rows.seq writer) initial read
    (GridPhysicalAdmission.Post a P rem _Y inner.records (2^w) (2^(3*w/5)) _source initial origin)
    _ _ _ admitted
  intro z hz mid post
  have decoded : GridSelector.decode D.run.plan table.codes (GridPhysicalSelector.bits D.run) cap sel=some (some z) := by
    simp only [GridSelector.decode,flag,ite_true]
    exact congrArg (Option.map some) hz
  let selected := (D.scheduled p z.1 C unit header advice (rooms z) cat reserved).1
  have written : (rows.seq writer).Spec (·=mid)
      (fun _ out=>GridOrderedSources.Raw cat selected enc arena B pins out capture) (2*2^(3*w/5)+time) :=
    issued hk axis hp hr hs machine fit hF state reps cat reserved params recv pins sel
      textFit axisFit cutFit dep setup maps depFit setupFit mapFit origin mid enough z (rooms z) decoded post
      pos rawSize small fitIdle roomIdle fitsWriter
  intro labels registers slots M pcMap regMap slotMap exit installed data cfg mem start eqn
  obtain ⟨t,bound,lastCfg,out,run,atExit,good⟩ :=
    written M pcMap regMap slotMap exit installed data cfg mem start eqn
  refine ⟨t,bound,lastCfg,out,run,atExit,?_⟩
  refine ⟨⟨good.controller.controller,good.controller.powers,good.controller.localData,?_⟩,good.exterior⟩
  intro i hi
  exact (good.controller.compact i hi).trans
    (congrFun (load_twice cat enc B (2*J) capture) (2*J+i)).symm

end Hierarchy.GridNativeController
end

end OAI
