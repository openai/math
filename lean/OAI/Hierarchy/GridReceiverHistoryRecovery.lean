import OAI.Hierarchy.GridPhysicalRegistration
import OAI.Hierarchy.TraceAdmissionWordRecovery
import OAI.Hierarchy.TraceNodeReceiverBounds
import OAI.ThreeFlat.Diagonal.TraceJournalWordGeometry

namespace OAI
/-! # Recovering the receiving tick's numbered word forest at its original S20 archive -/
namespace Hierarchy.GridPhysicalAdmission
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows RAM.PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution TraceAdmission TraceNodeHeaders NodePublication Filter
open scoped Classical Topology Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] (B : Block F)

/-- The resident header and its selected heap end below the first S40 guard. -/
theorem receiver_areas {w v : ℕ} (positive : 7≤w) (lower : 4*w≤v^10) (upper : v^10≤5*w) :
    let a:=TickWorkspace.base v 20
    21*(2^((64*w)/16))^4 ≤ a ∧
      a+7*traceUnit w+128≤TickWorkspace.base v 40 ∧ TickWorkspace.base v 45<2^(32*w) := by
  let step:=TickWorkspace.stride v
  have min0 : traceUnit w ≤ step := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (by omega : w≤v^10)) 4
  have hu : 128≤traceUnit w := by change 2^7≤(2^w)^4;rw [←pow_mul];exact Nat.pow_le_pow_right (by decide) (by omega)
  have small : (2^((64*w)/16))^4 ≤ step := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (by omega)) 4
  have top : TickWorkspace.base v 45<2^(32*w) := calc
    _ ≤ 2^6*step := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(6+v^10*4) := by simp only [step,TickWorkspace.stride,pow_add,pow_mul]
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)
  exact ⟨Nat.mul_le_mul_left 21 small,by change 21*step+7*traceUnit w+128≤41*step;omega,top⟩

/-- Every admitted compact tick reconstructs the public block templates on exactly the same
chosen path as the native node publisher. Raw words come from this tick's own history RAM. -/
theorem receiver_history {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {v pc regs words k size base fuel : ℕ}
      (lower : 4*w≤v^10) (upper : v^10≤5*w) (hk : 2≤k+1) (axis : k+1=u w+1-w/2)
      (machine : Machine (64*w) pc regs words) (fit : NativeTrace.Fits machine size base ((k+1)+w/2) fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (reps : B.blockCharge*s w≤k+1)
      (a : Archive) (place : ArchivePlacement a (TickWorkspace.base v 20) w)
      (ax : k+1=a.axes) (lanes : a.remainingLanes=2^(k+1)) (alphabet : a.K=B.alphabetCap)
      (deg : a.initialDegree=2^(B.exponent 0)) (source : ℕ→Bool) (input origin out : Memory (64*w)),
      let W:=64*w
      let depth:=(k+1)+w/2
      let g:=TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs words depth
      let off:=1+(depth+depth)
      let P:=B.repeat (s w)
      let rem:=k+1-P.charge
      let split : k+1=P.charge+rem:=by dsimp only [P,rem];rw [B.charge_repeat];omega
      let X:=B.cursorState hk (w/2) off g.cells
      let Y:State (2^B.exponent 0) (P.charge+rem):=split ▸ X
      let ss:=P.directory rem (k+1)
      let stop:=finish a.K ss a.cursor
      let x:=a.terminal ss (P.finalEdges rem (k+1)) W
      let O:=a.cursorSeedSites B hk (w/2) off g.cells ax lanes
      let r:=Physical.nativeRun B hk machine fit hF st (s w) reps
      let C:=(Physical.registerOnLanes B (Fin size→Bool) (s w) rem X split).2
      ∀ enough : B.repeatFactor*(X.maxWidth+1)*B.widthBase^(s w)<2^W,
        let inner:=B.recordTable B.alphabetCap W (s w) rem Y le_rfl
          (by rw [State.maxWidth_cast_lanes,←Nat.mul_assoc];exact enough)
        let table:=physicalTable B hk (w/2) off g.cells (s w) W reps enough
        Post a P rem Y inner.records (2^w) (2^(3*w/5)) source input origin out →
        ∃ (h : r.plan.History) (suffix : List Bool) (path : r.ArchivePath h C O) (mid : Memory W),
          r.plan.read table.codes (List.ofFn (fun j : Fin (2^(3*w/5))=>source j.val))=some (h,suffix) ∧
          r.FinalNumbered h C O path ∧ out=TerminalWireArchive.image x mid ∧
          (∀ (T : Type) (L : X.Words T), r.WordVisits (RecordedWordStep a.K (a.control:Word W)
            ((a.control+1:ℕ):Word W) stop.header stop.heap mid T B.publicTemplate)
            h (Physical.registerOnLanes B T (s w) rem X split).1.steps L C O path) ∧
          TraceRecovery.stagePost a.K ss a.cursor O.layer (·<a.control+64) (natural out)
            (directoryCap B) (directoryCap B) (fun _=>False)
            (r.archiveList h C O path a.seedData) (r.finalArchive h C O path).1 ∧ MountedAt (natural out) a.K ss a.cursor ∧
          a.cursor.header+64*ss.length≤a.control+64 ∧ stop.heap≤a.control+64 ∧
          (∀ z,a.initialRecords≤z → z<a.metadataEnd → mid z=origin z) ∧ (∀ z,z<a.seed → out z=input z) := by
  filter_upwards [eventual_recovery_geometry_at B scale,eventual_iteration_limits B scale,eventually_ge_atTop 7]
    with w memory limits hw
  intro v pc regs words k size base fuel lower upper hk axis machine fit hF st reps a place ax lanes alphabet deg
    source input origin out W depth g off P rem split X Y ss stop x O r C enough inner table post
  obtain ⟨headerLower,archiveTop,regionTop⟩:=receiver_areas hw lower upper
  have regions : TickWorkspace.base v 40≤TickWorkspace.base v 45 := Nat.mul_le_mul_right _ (by decide)
  have word : TickWorkspace.base v 45<2^W := regionTop.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [W];omega))
  have ctrl : (a.control:Word W).val=a.control := Fin.val_cast_of_lt (by rw [place.control];change _+6*traceUnit w<_;omega)
  have ctr : (a.control:Word W).val<((a.control+1:ℕ):Word W).val := by
    rw [ctrl,Fin.val_cast_of_lt (by rw [place.control];change _+6*traceUnit w+1<_;omega)];omega
  obtain ⟨halves,seedStart,seedEnd,curRoom,headRoom,nodeRoom,lastRoom⟩:=memory axis reps a _ place alphabet deg ax.symm lanes _ ctrl
  have it:=limits (reps.trans_eq axis) a _ 0 (a.control:Word W) alphabet place ctrl
  rw [←axis] at it
  have dense : stop.header≤a.cursor.dense := by
    have t:=it.tables
    rw [Archive.directory_length] at t
    change a.seed+64*(ss.length+2)≤a.cursor.dense at t
    have head:=it.origin
    change (finish a.K ss a.cursor).header≤_
    rw [header_finish];omega
  have baseEq : Fintype.card Y.Base=k+1 := (Program.baseCast split X).trans (Fintype.card_fin _)
  obtain ⟨initialVisit,reads,foot,keep,mid,⟨journal,ending⟩,img0⟩:=post
  let raw:=List.ofFn (fun j : Fin (2^(3*w/5))=>source j.val)
  have img : out=TerminalWireArchive.image x mid := by simpa only [baseEq] using img0
  have enoughWord : 8≤W := by dsimp [W];omega
  have smallWire : 2^w≤2^(W/16) := Nat.pow_le_pow_right (by decide) (by dsimp [W];omega)
  obtain ⟨h,suffix,path,decoded,num,vis,seen⟩:=repeated_word_recovery B hk reps a ax lanes alphabet enough (Fin size→Bool)
    _ _ raw origin mid journal (TraceRetainedRoom.native hw) enoughWord ctr reads foot halves seedStart seedEnd
    curRoom headRoom nodeRoom smallWire dense (headerLower.trans (by rw [place.header];omega))
  have mount:=compact_source_mounted P rem Y source raw journal initialVisit
    (by rw [place.header,place.seed]) (by simpa only [baseEq] using headRoom) curRoom ctr
  rw [baseEq] at mount
  have hp : a.cursor.header+64*ss.length≤x.prefixBase := by
    have head : (finish a.K ss a.cursor).header ≤ a.cursor.heap := headRoom
    rw [header_finish] at head
    change _ ≤ (finish a.K ss a.cursor).heap
    rw [heap_finish]
    omega
  have after:=Resources.after_terminal_guard (H:=a.control+64) x ss a.cursor O.layer
    (r.finalArchive h C O path).1 (r.archiveList h C O path a.seedData) mid seen mount hp lastRoom
  rw [←img] at after
  have seedFrame:=TraceWordRecovery.seed_records a P rem Y raw journal
    (by simpa only [baseEq] using seedStart) seedEnd curRoom ctr
  refine ⟨h,suffix,path,mid,decoded,num,img,vis,after.1,after.2,hp.trans lastRoom,lastRoom,seedFrame,?_⟩
  intro z low
  have below : z<x.prefixBase := by change z<(finish a.K ss a.cursor).heap;rw [heap_finish,place.heap];rw [place.seed] at low;omega
  have seedControl : a.seed ≤ (a.control : Word W).val := by
    rw [ctrl,place.seed,place.control]
    exact Nat.le_add_right ..
  have belowControl := low.trans_le seedControl
  have frame:=Archive.TraceJournal.frame P rem Y a.cursor raw journal
    belowControl.ne (belowControl.trans ctr).ne
    (show traceOutsideWrites a.K a.cursor (P.directory rem (Fintype.card Y.Base)) z from
      ⟨.inl (by rw [place.header];rw [place.seed] at low;omega),.inl (by rw [place.heap];rw [place.seed] at low;omega)⟩)
  have same : out z=mid z := by rw [img];simp [TerminalWireArchive.image,fillSegment,Nat.not_le_of_lt below]
  exact same.trans (frame.trans (keep z low))

end
end Hierarchy.GridPhysicalAdmission

end OAI
