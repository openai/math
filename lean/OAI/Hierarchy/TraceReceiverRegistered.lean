import OAI.Hierarchy.TraceReceiverAdmission
import OAI.Hierarchy.GridReceiverNodeRegistration

namespace OAI
/-! # The native archive and its selected node registration on one receiver execution -/
noncomputable section
namespace Hierarchy.TraceFactorReceiver
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows RAM.PhysicalProcedure RAM.TickStageSpec Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution TraceAdmission TraceNodeHeaders NodePublication Filter GridPhysicalAdmission
open scoped Classical Topology Fin.CommRing
variable {F : Type} [Field F] [Fintype F] (B : Block F)

/-- Accept the receiver's actual selector, run the native repeated navigator and terminal
checker, then publish and register its retained S43/S44 arrays on the same actual RAM.
The admitted procedure and successful parse are the two outputs of `admit` used here. -/
theorem publish {u s : ℕ→ℕ} (scale : Scale u s) (coef exp : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ {v pc regs words k size base fuel : ℕ}
      (lower : 4*w≤v^10) (upper : v^10≤5*w) (hk : 2≤k+1) (axis : k+1=u w+1-w/2)
      (hp : pc≤64*w) (hr : regs≤64*w) (hs : words≤64*w)
      (machine : Machine (64*w) pc regs words) (fit : NativeTrace.Fits machine size base ((k+1)+w/2) fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (reps : B.blockCharge*s w≤k+1)
      (a : Archive) (place : ArchivePlacement a (TickWorkspace.base v 20) w)
      (ax : k+1=a.axes) (lanes : a.remainingLanes=2^(k+1)) (alphabet : a.K=B.alphabetCap)
      (deg : a.initialDegree=2^(B.exponent 0)) (dirs band dep setup maps : ℕ)
      (directions : dirs≤w) (bandWidth : band ≤ size) (exterior : 2*(dirs*band) ≤ size)
      (depSize : dep≤coef*(w+1)^exp) (setupSize : setup≤coef*(w+1)^exp) (mapSize : maps≤coef*(w+1)^exp)
      (source : ℕ→Bool) (input origin : Memory (64*w)),
      let W:=64*w
      let depth:=(k+1)+w/2
      let grid:=TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs words depth
      let off:=1+(depth+depth)
      let P:=B.repeat (s w)
      let rem:=k+1-P.charge
      let split : k+1=P.charge+rem:=by dsimp only [P,rem];rw [B.charge_repeat];omega
      let X:=B.cursorState hk (w/2) off grid.cells
      let Y:State (2^B.exponent 0) (P.charge+rem):=split ▸ X
      let ss:=P.directory rem (k+1)
      let stop:=finish a.K ss a.cursor
      let x:=a.terminal ss (P.finalEdges rem (k+1)) W
      let last:=TraceRecovery.lastLayer a.K ss a.cursor a.seedLayer
      let O:=a.cursorSeedSites B hk (w/2) off grid.cells ax lanes
      let r:=Physical.nativeRun B hk machine fit hF st (s w) reps
      let C:=(Physical.registerOnLanes B (Fin size→Bool) (s w) rem X split).2
      let start:=TraceReceiverSeedWords.start machine fit hF st B hk
      let pairs:=TraceReceiverSeedWords.pairs machine fit hF st
      let desc:=TraceSourceOwner.shape W pc regs words size fuel depth grid.internal
      let trace:=TraceBitHeader.seedTraceWork (w/2) desc.stride grid.cells B.cursorCopies depth
      let unit:=FactorWork.archiveTariff w dep setup maps P.length B.localCoefficient
      let node:=receiverArchive v (2^(k+1)) (2^(w/2)) ((size+1)/2) trace unit (directoryCap B) (directoryCap B) (directoryCap B)
      let p:=Resources.gridRows w (2^(k+1)) last.count dirs (2^(w/2)) band size node.banks.charges last.first
      let hdr:=a.control+64
      let dst:=14*2^(32*w)
      let D:=traceLimit w+ss.length*p.lanes
      a.relayWidth=2^(w/2)*(off*grid.cells*3) →
      ∀ enough : B.repeatFactor*(X.maxWidth+1)*B.widthBase^(s w)<2^W,
        let inner:=B.recordTable B.alphabetCap W (s w) rem Y le_rfl
          (by rw [State.maxWidth_cast_lanes,←Nat.mul_assoc];exact enough)
        let table:=physicalTable B hk (w/2) off grid.cells (s w) W reps enough
        let stages:=GridPhysicalAdmission.program B a ss (P.finalEdges rem (k+1)) W (s w)
        let reg:=Resources.registerNodes W (TickWorkspace.base v 41) hdr (traceLimit w) a.cursor.header
          ss.length dst node O.layer p
        let post:=fun _ out : Memory W=>Post a P rem Y inner.records (2^w) (2^(3*w/5)) source input origin out
        ∀ (valid : Memory W→Prop) (cost : ℕ),
        Admission (FieldCode.ofCardLe hF) stages.block stages.publicData (·=input) valid post cost →
        valid input →
        (stages.seq reg).Spec (·=input) (fun _ after=>∃ out,post input out ∧
          ∃ (h : r.plan.History) (suffix : List Bool) (path : r.ArchivePath h C O)
          (mid : Memory W) (count : Fintype.card (r.plan.finish h).Site=p.roots),
          r.plan.read table.codes (List.ofFn (fun j : Fin (2^(3*w/5))=>source j.val))=some (h,suffix) ∧
          r.FinalNumbered h C O path ∧ out=TerminalWireArchive.image x mid ∧
          (∀ (T : Type) (L : X.Words T),r.WordVisits (RecordedWordStep a.K (a.control:Word W) ((a.control+1:ℕ):Word W)
            stop.header stop.heap mid T B.publicTemplate) h (Physical.registerOnLanes B T (s w) rem X split).1.steps L C O path) ∧
          let idx:=Resources.indexEquiv r h count
          let dest:=fun j=>idx (r.plan.destination h (initialLane (Nat.succ_pos k) j))
          let work:=fun f=>unit*r.chargeAt h C start (idx.symm f)
          Resources.Registered D dst p dest work after ∧
              (∀ z,z<a.seed → after z=input z) ∧
              (∀ z,z<hdr → after z=out z) ∧
              ∃ saved : Memory W,O.Charged node.banks (natural saved) start pairs ∧
                r.ArchiveRowsStored node.banks (natural saved) h C O path ∧
                (∀ z,TickWorkspace.base v 43≤z → z<TickWorkspace.base v 45 → after z=saved z) ∧
                TraceRecovery.stagePost a.K ss a.cursor O.layer (·<hdr) (natural out)
                  (directoryCap B) (directoryCap B) (fun _=>False)
                  (r.archiveList h C O path a.seedData) (r.finalArchive h C O path).1 ∧
                MountedAt (natural out) a.K ss a.cursor ∧
                (∀ z,a.initialRecords≤z → z<a.metadataEnd → mid z=origin z) ∧
                ReceiverCache v a.cursor.header ss.length (rowBudget W node ((k+1)*2^(k+1))) stop.heap
                  node O.layer (r.archiveList h C O path a.seedData) mid out saved after) (cost+2*2^(3*w/5)) := by
  filter_upwards [register_receiver_post B scale coef exp] with w registered
  intro v pc regs words k size base fuel lower upper hk axis hp hr hs machine fit hF st reps a place ax lanes alphabet deg
    dirs band dep setup maps directions bandWidth exterior depSize setupSize mapSize source input origin
    W depth grid off P rem split X Y ss stop x last O r C start pairs desc trace unit node p hdr dst D wire enough
    inner table stages reg post valid cost admission accepted
  let preReg:=fun out=>post input out
  have nav : stages.Spec (·=input) post cost := by
    intro labels registers slots M
    exact positive (FieldCode.ofCardLe hF) stages admission (by rintro _ rfl;exact accepted) M
  let selected:=fun out after : Memory W=>
    ∃ (h : r.plan.History) (suffix : List Bool) (path : r.ArchivePath h C O)
          (mid : Memory W) (count : Fintype.card (r.plan.finish h).Site=p.roots),
          r.plan.read table.codes (List.ofFn (fun j : Fin (2^(3*w/5))=>source j.val))=some (h,suffix) ∧
          r.FinalNumbered h C O path ∧ out=TerminalWireArchive.image x mid ∧
          (∀ (T : Type) (L : X.Words T),r.WordVisits (RecordedWordStep a.K (a.control:Word W) ((a.control+1:ℕ):Word W)
            stop.header stop.heap mid T B.publicTemplate) h (Physical.registerOnLanes B T (s w) rem X split).1.steps L C O path) ∧
          let idx:=Resources.indexEquiv r h count
          let dest:=fun j=>idx (r.plan.destination h (initialLane (Nat.succ_pos k) j))
          let work:=fun f=>unit*r.chargeAt h C start (idx.symm f)
          Resources.Registered D dst p dest work after ∧
              (∀ z,z<a.seed → after z=input z) ∧
              (∀ z,z<hdr → after z=out z) ∧
              ∃ saved : Memory W,O.Charged node.banks (natural saved) start pairs ∧
                r.ArchiveRowsStored node.banks (natural saved) h C O path ∧
                (∀ z,TickWorkspace.base v 43≤z → z<TickWorkspace.base v 45 → after z=saved z) ∧
                TraceRecovery.stagePost a.K ss a.cursor O.layer (·<hdr) (natural out)
                  (directoryCap B) (directoryCap B) (fun _=>False)
                  (r.archiveList h C O path a.seedData) (r.finalArchive h C O path).1 ∧
                MountedAt (natural out) a.K ss a.cursor ∧
                (∀ z,a.initialRecords≤z → z<a.metadataEnd → mid z=origin z) ∧
                ReceiverCache v a.cursor.header ss.length (rowBudget W node ((k+1)*2^(k+1))) stop.heap
                  node O.layer (r.archiveList h C O path a.seedData) mid out saved after
  have stored : reg.Spec preReg selected (2*2^(3*w/5)) := by
    intro pc regs kk M loc rr pub exit rom data cfg out entry ready
    obtain ⟨h,suffix,path,mid,count,read,number,term,vis,actual⟩ :=
      registered lower upper hk axis hp hr hs machine fit hF st reps a place ax lanes alphabet deg
        dirs band dep setup maps directions bandWidth exterior depSize setupSize mapSize source input origin out
        wire enough ready
    obtain ⟨t,ht,c,m,go,endPc,data⟩:=actual M loc rr pub exit rom data cfg out entry rfl
    exact ⟨t,ht,c,m,go,endPc,h,suffix,path,mid,count,read,number,term,vis,data⟩
  intro nPC nRegs nPub M
  exact Procedure.Spec.seq (A:=stages) (B:=reg) (pre:=(·=input)) (mid:=preReg)
    (left:=post) (right:=selected) nav stored (fun _ _ h=>h) M

end Hierarchy.TraceFactorReceiver
end

end OAI
