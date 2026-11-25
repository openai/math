import OAI.Hierarchy.GridRegisteredPublication
import OAI.Hierarchy.GridPhysicalRegistration
import OAI.Hierarchy.GridSelectorHistory

namespace OAI
/-! # Executing the registered emitter after a successful physical history scan

The terminal archive and the selector decoder recover the same history.
Registration and publication run consecutively on the live machine memory.
Both stages take their program sizes from the public directory.
-/

noncomputable section
namespace Hierarchy.GridPhysicalEmission
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows RAM.PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution TraceAdmission TraceNodeHeaders NodePublication GridRegisteredSetting Filter
open scoped Classical Topology Fin.CommRing

variable {F : Type} [Field F] [Fintype F] (blk : Block F)

theorem post_raw {u s : ℕ → ℕ} (scale : Scale u s) (coef exp : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ {pc regs words k S base fuel : ℕ} (hk : 2 ≤ k+1)
      (axis : k+1=u w+1-w/2) (hp : pc ≤ 64*w) (hr : regs ≤ 64*w) (hs : words ≤ 64*w)
      (machine : Machine (64*w) pc regs words) (fit : NativeTrace.Fits machine S base ((k+1)+w/2) fuel)
      (hF : Fintype.card F ≤ 2^(64*w)) (state : Word (64*w)) (reps : blk.blockCharge*s w ≤ k+1)
      {m n B q d np cap text tp tr tk logRadix : ℕ}
      (cat : Catalyst.Approximation F (m+1) (q*d)) (reserved : ∀ j,cat.width j ≤ B)
      (params : Fin np → Word (64*w)) (recv : Machine (64*w) tp tr tk)
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
      let Y : State (2^blk.exponent 0) (P.charge+rem) := split ▸ X
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
      let capture := GridPinPublisher.capture (compact:=B) cat enc params recv machine pins sel
      let initial := GridApproximationAdvice.paddedMemory cat enc B (2*J) capture
      let source := GridStructuralHeader.selectorBit cap sel
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
      ∀ (origin out : Memory W) (enough : blk.repeatFactor*(X.maxWidth+1)*blk.widthBase^(s w) < 2^W),
        let inner := blk.recordTable blk.alphabetCap W (s w) rem Y le_rfl
          (by rw [State.maxWidth_cast_lanes,←Nat.mul_assoc]; exact enough)
        let table := physicalTable blk hk (w/2) off grid.cells (s w) W reps enough
        ∀ (z : D.trace) (room : D.Room z.1 C unit w m n B q d header),
        GridSelector.decode D.run.plan table.codes (GridPhysicalSelector.bits D.run) cap sel=some (some z) →
        GridPhysicalAdmission.Post a P rem Y inner.records (2^w) (2^(3*w/5)) source initial origin out →
        0 < q*d → GridSelfHeader.rawSize w rails B np ≤ S →
        GridPinArena.Small w (GridPinPublisher.canonical w (m+1) n q d np (cap+1) text B rails S last.count
          ss.length full (2*span)) S full (ss.length*full) ((20*(w+1)+2)^((m+1)+2)) →
        GridControllerIdle.Fits W arena arch → GridControllerIdle.Room arena arch →
        GridOrderedSources.Fits (r:=rails) (n:=n) (w:=W) cat arena B →
        (rows.seq writer).Spec (·=out) (fun _ final => GridOrderedSources.Raw cat
          (D.scheduled p z.1 C unit header advice room cat reserved).1 enc arena B pins final capture)
          ((2*2^(3*w/5))+time) := by
  filter_upwards [GridPhysicalAdmission.register_post blk scale coef exp,
    eventual_record_length blk scale,eventually_ge_atTop 1] with w register recordLength age
  intro pc regs words k S base fuel hk axis hp hr hs machine fit hF state reps
    m n B q d np cap text tp tr tk logRadix cat reserved params recv pins sel textFit axisFit cutFit
    dep setup maps depFit setupFit mapFit W J rails full span depth grid off static a P rem split X Y ss last D C O
    desc trace unit node band p enc capture initial source header advice arena arch rows writer time origin out
    enough inner table z room decode post positive rawSize small geomFit geomRoom space
  have external : 2*((m+1)*band) ≤ S := room.external
  have bandFit : band ≤ S := calc
    band ≤ (m+1)*band := Nat.le_mul_of_pos_left band (Nat.succ_pos m)
    _ ≤ 2*((m+1)*band) := Nat.le_mul_of_pos_left _ (by decide : 0<2)
    _ ≤ S := external
  obtain ⟨seen,suffix,path,count,parsed,_,registration⟩ := register hk axis hp hr hs machine fit hF state reps
    cap static (m+1) band dep setup maps axisFit bandFit external depFit setupFit mapFit
    source initial origin out enough post
  have fixed (h : D.run.plan.History) : (D.run.plan.write table.codes h).length ≤ 2^(3*w/5) := by
    rw [table.write_size]
    have bound := recordLength (axis ▸ reps)
    simpa only [W,←axis,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using bound
  have window : (List.ofFn (Fin.tail sel)).take (2^(3*w/5)) =
      List.ofFn (fun j : Fin (2^(3*w/5)) => source j.val) := by
    have body : List.ofFn (fun j : Fin cap => source j.val) = List.ofFn (Fin.tail sel) :=
      GridStructuralHeader.selector_body (cap:=cap) sel
    exact (congrArg (fun bits : List Bool => bits.take (2^(3*w/5))) body.symm).trans
      (GridSelector.take_window source cutFit)
  have decoded : seen=z.1 := GridSelector.recovered_eq D.run.plan table.codes (GridPhysicalSelector.bits D.run)
    cap sel (2^(3*w/5)) fixed z decode seen suffix (by rw [window]; exact parsed)
  subst seen
  have emit {targetPC targetRegisters targetSlots : ℕ} (target : Machine W targetPC targetRegisters targetSlots) := GridRegisteredPublication.run D p z.1 C unit cat enc params recv pins sel textFit room reserved
    count (by omega) axisFit positive rawSize small geomFit geomRoom space target
  intro targetPC targetRegisters targetSlots target pcEntry reg pub exit rom hardware cfg mem start initialMem
  obtain ⟨ticks,within,final,output,advance,atExit,_,_,received⟩ :=
    Procedure.Spec.seq registration (@emit) (by
      intro _ after saved
      refine ⟨saved.1,GridRegisteredPublication.low_of_register (seed:=a.seed)
        (extent:=Resources.resourceLength p) ?_ saved.2.1⟩
      change 13*J ≤ 16*J
      omega) target pcEntry reg pub exit rom hardware cfg mem start initialMem
  exact ⟨ticks,within,final,output,advance,atExit,received⟩

end Hierarchy.GridPhysicalEmission
end

end OAI
