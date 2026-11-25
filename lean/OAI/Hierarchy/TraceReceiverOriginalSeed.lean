import OAI.Hierarchy.TraceReceiverCofinalHalves
import OAI.Hierarchy.TraceReceiverCofinalPrices
import OAI.Hierarchy.GridChosenReceiverPrefix

namespace OAI
/-! # Original rows and coordinates of the genuinely initialized receiver seed -/

namespace Hierarchy.TraceReceiverOriginalSeed
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.PhysicalProcedure RAM.NavigationNodeRows Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution TraceAdmission GridRegisteredSetting GridReceiverDirectory Filter
open scoped Classical Fin.CommRing Topology
noncomputable section
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [Fintype F]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
/-- The actual shifted tape, the decoder's header and the common work bound on its registered
roots determine all five literal seed words and all initial half rows. -/
theorem geometry (B : Block F) {depth reps : ℕ→ℕ} (scale : Scale depth reps) :
    ∀ᶠ w : ℕ in atTop,∀ {pc regs words size addr fuel axes : ℕ} (hk : 2≤axes+1)
      (_axis : axes+1=depth w+1-w/2) (_hp : pc≤64*w) (_hr : regs≤64*w) (_hw : words≤64*w)
      (M : Machine (64*w) pc regs words) (ft : NativeTrace.Fits M size addr ((axes+1)+w/2) fuel)
      (field : Fintype.card F≤2^(64*w)) (state : Word (64*w)) (fit : B.blockCharge*reps w≤axes+1),
      let I : RunData F (64*w) pc regs words size addr fuel axes (w/2):=⟨M,ft,field,state,B,hk,reps w,fit⟩
      ∀ (l : GridNativeImage.Layout) (h : I.run.plan.History) (sel : Fin (l.selectorCap+1)→Bool)
        (textFit : SelfAdvice.textSize (64*w) pc words≤w^2) (self : Fin (w^2)→Bool)
        (tick : Word (64*w)) (input : ℕ→Bool),
        let G:=TraceStaticRow.gateTable field ft.width ft.labels addr fuel state regs words ((axes+1)+w/2)
        let off:=1+(((axes+1)+w/2)+((axes+1)+w/2))
        let a:=archive I l
        let dir:=native I l
        let stop:=finish a.K dir.stages a.cursor
        let O:=a.cursorSeedSites B hk (w/2) off G.cells rfl rfl
        let origin:=original I l sel input
        let ps:=GridStructuralHeader.parameters B (axes+1) (reps w) l.selectorCap M ft field state
          0 (26*GridDescription.sector w)
        let head:=GridReceiverHeader.header _ textFit self tick ps sel
        head.length≤l.pinWidth → 2+head.length≤a.seed →
        TraceFactorReceiver.Selector.headerReads _ textFit self tick ps sel input →
        2^(3*w/5)≤l.selectorCap → 0<dir.node.banks.unitWork →
        (∀ i,I.work h I.issuedCharges dir.node.banks.unitWork i≤2^(3*w/5)) →
        stop.heap≤a.control+64 ∧ a.metadataEnd≤a.cursor.heap ∧ a.K<2^(64*w) ∧
        State.HalfRows O (fun i=>a.initialRecords ≤ i ∧ i<a.metadataEnd) (fun i=>(origin i).val) ∧
        ∀ i : Fin a.initialSites,∀ c : Fin 5,origin (a.initialRecords+5*i.val+c.val)=
          ((![a.seed,i.val,0,i.val%a.remainingLanes,i.val/a.remainingLanes] : Fin 5→ℕ) c : Word (64*w)) := by
  let rate:=3*5*10^26*65^14
  filter_upwards [TraceCompactSeed.eventual_resources B scale rate 15,eventual_native_port_count (F:=F) scale,
    eventual_record_length B scale,eventual_recovery_geometry_at B scale,eventually_ge_atTop (64^10),
    eventually_ge_atTop B.alphabetCap] with w material ports length recover big alphabet
  intro pc regs words size addr fuel axes hk _axis _hp _hr _hw M ft field st fit I l h sel textFit self tick input
    G off a dir stop O origin ps head padded headLow read cutFits unit work
  let W:=64*w
  let beta:=GridStructuralHeader.recipientBase w
  let P:=B.repeat (reps w)
  let rem:=axes+1-P.charge
  let ss:=P.directory rem (axes+1)
  have pos : 0<w := (by decide : 0<64^10).trans_le big
  have scaleBounds:=receiverAge_chart w big
  have top:=TraceCompactSeed.recipient_top pos scaleBounds.1 scaleBounds.2
  have small : a.phase+1+l.selectorCap≤beta := by
    rw [GridReceiverHeader.length] at headLow
    change 2+SelfAdvice.textSize W pc words+(GridNativeImage.parameterCount I l+1)*W+
      GridReceiverHeader.count w*W+1+l.selectorCap≤beta
    change 2+(SelfAdvice.textSize W pc words+((GridNativeImage.parameterCount I l+1)*W+
      (GridReceiverHeader.count w*W+(l.selectorCap+1))))≤beta at headLow
    omega
  have placed:=TraceCompactSeed.archive_placement B w beta (axes+1) off G.cells l.selectorCap a.rawStatic a.phase
  have ptr : a.control<2^W := by
    calc
      beta+6*(2^w)^4 ≤ beta+8*(2^w)^4 :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (by decide : 6 ≤ 8)) beta
      _ < 2^W := top
  have range:=recover _axis fit a beta placed rfl rfl rfl rfl (a.control:Word W) (Fin.val_cast_of_lt ptr)
  obtain ⟨seed,limits,terminal,clock⟩:=material beta axes off G.cells l.selectorCap a.rawStatic a.phase
    fit _axis (ports _hp _hr _hw _axis M ft field st) small top
  have coded : (stageCounts B (reps w) (axes+1)).sum*B.alphabetCap*W≤2^(3*w/5) := by
    rw [_axis]
    exact length (_axis ▸ fit)
  have hist : W*a.histWords ss≤2^(3*w/5) := by
    simpa only [a,archive,TraceCompactSeed.archive,Archive.histWords,stageCounts,ss,P,rem,
      Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using coded
  let witness : (B.cursorState hk (w/2) off G.cells).Site:=(0,fun _=>0)
  have relay : 2*a.initialDegree*a.relayWidth<2^(3*w/5) :=
    TraceReceiverCofinalPrices.relay_bound I h dir.node.banks unit work witness
  have sumWord : 2*a.initialDegree*a.relayWidth<2^W :=
    relay.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨range.2.2.2.2.2.2,range.2.2.1,(show B.alphabetCap≤W by omega).trans_lt Nat.lt_two_pow_self,?_,?_⟩
  · exact TraceCompactSeed.initial_half_rows B (axes+1) (reps w) l.selectorCap off G.cells M ft field st
      0 (26*GridDescription.sector w) textFit self tick sel input padded read hk rfl headLow
      (hist.trans cutFits) seed limits terminal sumWord
  · exact TraceCompactSeed.initial_kernel B (axes+1) (reps w) l.selectorCap off G.cells M ft field st
      0 (26*GridDescription.sector w) textFit self tick sel input padded read hk rfl headLow
      (hist.trans cutFits) seed limits terminal

end
end Hierarchy.TraceReceiverOriginalSeed

end OAI
