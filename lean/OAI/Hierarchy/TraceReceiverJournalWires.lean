import OAI.Hierarchy.TraceReceiverElectedJournal

namespace OAI
/-! # Terminal widths and prefix words in the selected receiving journal -/

noncomputable section
namespace Hierarchy.TraceReceiverElectedJournal

open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows RAM.PhysicalProcedure RAM.TickStageSpec Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution TraceAdmission TraceNodeHeaders NodePublication GridRegisteredSetting GridPhysicalAdmission
open TraceFactorReceiver.Gather Filter GridReceiverDirectory
open scoped Classical Topology Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {w pc rr pp size base fuel axes : ℕ}

/-- The terminal width bank and prefix computation use the same canonical edge order as the
selected compressed graph. All addresses in this receipt are actual live memory addresses. -/
structure TerminalWires {wrd d laneCount : ℕ} (age fence : ℕ) (layout : TerminalWireArchive.Layout)
    (S : State d laneCount) (mid registered : Memory wrd) : Prop where
  start : TickWorkspace.base age 18+TickWorkspace.stride age ≤ layout.prefixBase
  stop : layout.prefixBase+S.edgeCount ≤ fence
  archiveStart : TickWorkspace.base age 20≤layout.prefixBase
  beforeLibrary : layout.prefixBase+S.edgeCount<TickWorkspace.base age 38
  bounds : TerminalWireArchive.Bounds layout wrd
  edges : layout.edges=S.edgeCount
  widths : ∀ i : Fin S.edgeCount,(mid (layout.widthBase+i.val)).val=S.wireWidth i
  capacity : S.widthSum≤layout.capacity
  emitted : ∀ i : Fin (S.edgeCount+1),
    registered (layout.prefixBase+i.val)=TerminalWireArchive.image layout mid (layout.prefixBase+i.val)

section
variable (D : RunData F (64*w) pc rr pp size base fuel axes (w/2)) (l : GridNativeImage.Layout)
set_option quotPrecheck false
local notation "W" => (64*w)
local notation "B" => D.block
local notation "a" => archive D l
local notation "dir" => native D l
local notation "depth" => ((axes+1)+w/2)
local notation "G" => TraceStaticRow.gateTable D.field D.fit.width D.fit.labels base fuel D.state rr pp depth
local notation "off" => (1+(depth+depth))
local notation "P" => (D.block.repeat D.passes)
local notation "rem" => (axes+1-(P).charge)
local notation "X" => D.block.cursorState D.axesFit (w/2) off (G).cells
local notation "ss" => (dir).stages
local notation "edges" => (dir).edges
local notation "u" => TraceAdmission.receiverAge w
local notation "stop" => finish (a).K ss (a).cursor
local notation "x" => (a).terminal ss edges W
local notation "O" => (a).cursorSeedSites D.block D.axesFit (w/2) off (G).cells rfl rfl
local notation "C" => D.issuedCharges
local notation "start" => TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit
local notation "pairs" => TraceReceiverSeedWords.pairs D.machine D.fit D.field D.state
local notation "node" => (dir).node
local notation "par" => (dir).parameters
local notation "N" => (par).roots
local notation "hdr" => (a).control+64
local notation "destAddr" => (traceLimit w+(ss).length*(par).lanes)
local notation "dst" => (14*GridDescription.sector w)
local notation "cut" => (2^(3*w/5))
local notation "cap" => l.selectorCap
local notation "bits" => GridPhysicalSelector.bits D.run
local notation "units" => D.issuedUnit w l.degree l.stageRate l.rootRate
local notation "T" => ((l.sideMinusOne+1)^(l.dimension+1)*l.copies)
local notation "d" => ((l.dimension+1)+2)
local notation "text" => SelfAdvice.textSize W pc pp
local notation "args" => GridNativeImage.parameterCount D l
local notation "choose" => GridReceiverTickDirectory.receiver w u text args N d T
local notation "histTime" => (cut+(cut+Archive.terminalTime x))
local notation "nav" => TraceReceiverProgram.navigation D.block W dir
local notation "splitLanes" => (by rw [D.block.charge_repeat]; have := D.passesFit; omega :
  axes+1=(P).charge+rem)
local notation "Y" => (splitLanes ▸ X : State (2^D.block.exponent 0) ((P).charge+rem))

variable (geom : ElectionRoom D l) (safe : GridNativeDispatch.WordRoom D)
    (z : D.trace) (sel : Fin (l.selectorCap+1) → Bool)
    (t : Fin ((l.sideMinusOne+1)^(l.dimension+1)*l.copies))
    (input origin endState : Memory (64*w))
local notation "costRows" => (D.costs (GridNativeImage.resources D l) z.1 l.dimension l.sideMinusOne l.bank C units)
local notation "source" => GridStructuralHeader.selectorBit cap sel
local notation "table" => (B).recordTable (B).alphabetCap W D.passes rem Y le_rfl
  (by rw [State.maxWidth_cast_lanes,←Nat.mul_assoc];exact safe)


theorem Journal.wires (j : Journal D l geom safe z sel t input origin endState)
    (big : 64^10≤w) (space : (a).TerminalRoom ss edges W)
    (selectorSpace : GridSelector.Room D.run.plan (GridNativeDispatch.actualTable D safe).codes bits cap) :
    TerminalWires u (30*GridDescription.sector w-16) x (D.run.terminalLayer z.1).state j.mid j.reg := by
  let raw:=List.ofFn (fun i : Fin cut=>source i.val)
  let S:=(D.run.terminalLayer z.1).state
  have card : Fintype.card (Y).Base=axes+1 := (Program.baseCast splitLanes X).trans (Fintype.card_fin _)
  have stagesEq : ss = (P).directory rem (axes+1) := rfl
  have edgesEq : edges = (P).finalEdges rem (axes+1) := rfl
  obtain ⟨_,_,_,_,other,⟨_,v,ends,visit⟩,snapshot⟩:=j.initial
  obtain ⟨inner,innerRead,innerEnd⟩:=ends
  have countV : edges=v.state.edgeCount := by
    rw [edgesEq,←innerEnd]
    simpa only [card] using ((P).finalEdges_eq rem Y inner).symm
  have reaches : D.run.EndsAt (GridNativeDispatch.actualTable D safe).records raw v
      (raw.drop (W*(a).histWords ss)) := by
    apply (Program.endsAt_changeTable splitLanes X _ table _ _ _).mpr
    exact ⟨inner,by simpa only [card,stagesEq] using innerRead,innerEnd⟩
  obtain ⟨selected,read,last⟩:=reaches
  have agreed : (selected,raw.drop (W*(a).histWords ss))=(z.1,j.suffix) :=
    Option.some.inj (read.symm.trans j.read)
  have selectedEq : selected=z.1 := congrArg Prod.fst agreed
  subst selected
  cases last
  have edgeCount : edges=S.edgeCount := countV
  have stored : (a).Visit ss edges source ((a).control : Word W) ss S other := by
    simpa only [card, ← stagesEq, ← edgesEq] using visit
  have oldImage : j.out = TerminalWireArchive.image x other := by
    simpa only [card, ← stagesEq, ← edgesEq] using snapshot
  have such (i : Fin S.edgeCount) : (j.mid ((x).widthBase+i.val)).val=S.wireWidth i := by
    have below : (x).widthBase+i.val < (x).prefixBase :=
      (Nat.add_lt_add_left i.isLt _).trans_le stored.widthBound
    have same : other ((x).widthBase+i.val)=j.mid ((x).widthBase+i.val) := by
      have eqn:=congrFun (oldImage.symm.trans j.terminal) ((x).widthBase+i.val)
      simpa only [TerminalWireArchive.image,fillSegment,not_le_of_gt below,false_and,ite_false] using eqn
    rw [←same]
    exact NavigationPass.stored_width_word S _ other stored.stored i
  have historyLength : (D.run.plan.write (GridNativeDispatch.actualTable D safe).codes z.1).length=W*(a).histWords ss := by
    rw [(GridNativeDispatch.actualTable D safe).write_size]
    change ((ss).map Stage.motifs).sum*D.block.alphabetCap*W =
      W*(D.block.alphabetCap*((ss).map Stage.motifs).sum)
    ac_rfl
  have wireFit := selectorSpace z.1
  rw [historyLength] at wireFit
  have capacity : S.widthSum≤(x).capacity :=
    Nat.le_sub_of_add_le (by change S.widthSum+W*(a).histWords ss≤cap;simpa only [Nat.add_comm] using wireFit)
  obtain ⟨ageLo,ageHi⟩:=receiverAge_chart w big
  obtain ⟨_,upper,limits⟩:=GridPhysicalAdmission.receiver_areas (by omega : 7≤w) ageLo ageHi
  have control : (a).control=TickWorkspace.base u 20+6*traceUnit w := rfl
  have heapLo : TickWorkspace.base u 18+TickWorkspace.stride u≤(x).prefixBase := by
    apply Nat.le_trans _ space.seed
    change 19*TickWorkspace.stride u+TickWorkspace.stride u≤21*TickWorkspace.stride u
    omega
  have le45 := Nat.mul_le_mul_right (TickWorkspace.stride u) (by decide : 41≤46)
  have control40 : (a).control ≤ TickWorkspace.base u 40 := calc
    (a).control = TickWorkspace.base u 20+6*traceUnit w := control
    _ ≤ TickWorkspace.base u 20+7*traceUnit w+128 := by omega
    _ ≤ TickWorkspace.base u 40 := upper
  have small : (a).control < 2^(32*w) :=
    (control40.trans (show TickWorkspace.base u 40 ≤ TickWorkspace.base u 45 from le45)).trans_lt limits
  have lastWord : (x).prefixBase+S.edgeCount < (a).control := by
    rw [←edgeCount]
    exact space.control
  have fence : (x).prefixBase+S.edgeCount≤30*GridDescription.sector w-16 := by
    change _≤30*2^(32*w)-16
    have positive := Nat.two_pow_pos (32*w)
    omega
  have unitBound : traceUnit w ≤ TickWorkspace.stride u :=
    Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (by omega : w≤u^10)) 4
  have beforeLibrary : (x).prefixBase+S.edgeCount<TickWorkspace.base u 38 := by
    apply lastWord.trans_le
    rw [control]
    change 21*TickWorkspace.stride u+6*traceUnit w≤39*TickWorkspace.stride u
    omega
  refine ⟨heapLo,fence,space.seed,beforeLibrary,space.bounds,edgeCount,such,capacity,?_⟩
  intro i
  have addr : (x).prefixBase+i.val < (a).control :=
    (Nat.add_le_add_left (Nat.le_of_lt_succ i.isLt) (x).prefixBase).trans_lt lastWord
  exact (j.archived _ (addr.trans_le (Nat.le_add_right _ 64))).trans (congrFun j.terminal _)

end

/-- Cofinal native layout bounds using the actual end of the compact header tape. -/
theorem eventual_wire_room (B : Block F) {depthFn passes : ℕ→ℕ} (scale : Scale depthFn passes) :
    ∀ᶠ w : ℕ in atTop, ∀ {pc regs words size addr fuel axes : ℕ} (hk : 2≤axes+1)
      (_axis : axes+1=depthFn w+1-w/2) (M : Machine (64*w) pc regs words)
      (ft : NativeTrace.Fits M size addr ((axes+1)+w/2) fuel) (field : Fintype.card F≤2^(64*w))
      (st : Word (64*w)) (fit : B.blockCharge*passes w≤axes+1),
      let I : RunData F (64*w) pc regs words size addr fuel axes (w/2):=⟨M,ft,field,st,B,hk,passes w,fit⟩
      ∀ (l : GridNativeImage.Layout) (sel : Fin (l.selectorCap+1)→Bool)
        (textFit : SelfAdvice.textSize (64*w) pc words≤w^2) (self : Fin (w^2)→Bool) (tick : Word (64*w)),
        let ps:=GridStructuralHeader.parameters B (axes+1) (passes w) l.selectorCap M ft field st
          0 (26*GridDescription.sector w)
        let ar:=archive I l
        let n:=native I l
        2+(GridReceiverHeader.header _ textFit self tick ps sel).length≤ar.seed →
        ar.TerminalRoom n.stages n.edges (64*w) := by
  filter_upwards [eventual_terminal_room_at B scale,eventually_ge_atTop (64^10)] with w space big
  intro pc regs words size addr fuel axes hk _axis M ft field st fit I l sel textFit self tick ps ar n lowHead
  let width:=64*w
  let beta:=GridStructuralHeader.recipientBase w
  let rows:=TraceStaticRow.gateTable field ft.width ft.labels addr fuel st regs words ((axes+1)+w/2)
  let off:=1+(((axes+1)+w/2)+((axes+1)+w/2))
  have placed:=TraceCompactSeed.archive_placement B w beta (axes+1) off rows.cells l.selectorCap ar.rawStatic ar.phase
  have small : ar.phase+1+l.selectorCap≤beta := by
    rw [GridReceiverHeader.length] at lowHead
    change 2+SelfAdvice.textSize width pc words+(GridNativeImage.parameterCount I l+1)*width+
      GridReceiverHeader.count w*width+1+l.selectorCap≤beta
    change 2+(SelfAdvice.textSize width pc words+((GridNativeImage.parameterCount I l+1)*width+
      (GridReceiverHeader.count w*width+(l.selectorCap+1))))≤beta at lowHead
    omega
  have bounded:=receiverAge_chart w big
  have top:=TraceCompactSeed.recipient_top ((by decide : 0<64^10).trans_le big) bounded.1 bounded.2
  have cert:=space (fit.trans_eq _axis) ar beta placed rfl top (by omega) small small
  let program := B.repeat (passes w)
  let slack := axes+1-program.charge
  have stages_eq : n.stages = program.directory slack (axes+1) := rfl
  have edges_eq : n.edges = program.finalEdges slack (axes+1) := rfl
  rw [stages_eq,edges_eq]
  simpa only [slack,program,←_axis] using cert.2

end Hierarchy.TraceReceiverElectedJournal
end

end OAI
