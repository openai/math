import OAI.Hierarchy.GridReceiverDirectoryElection
import OAI.Hierarchy.TraceReceiverWireBits
import OAI.Hierarchy.GridReceiverPrefixClock

namespace OAI
/-! # Independent navigation, registration and election in the actual receiving program -/

noncomputable section
open scoped Fin.CommRing

namespace Hierarchy.GridReceiverDirectory

open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows RAM.PhysicalProcedure RAM.TickStageSpec Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution TraceAdmission TraceNodeHeaders NodePublication GridRegisteredSetting GridPhysicalAdmission
open TraceFactorReceiver.Gather Filter
open scoped Classical Topology

variable {F : Type} [Field F] [Fintype F]

section
variable {w pc rr pp size base fuel axes : ℕ}
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

def Histories (z : D.trace) (sel : Fin (cap+1)→Bool) (safe : GridNativeDispatch.WordRoom D)
    (input origin after : Memory W) : Prop :=
  let source := GridStructuralHeader.selectorBit cap sel
  let table := (B).recordTable (B).alphabetCap W D.passes rem Y le_rfl
    (by rw [State.maxWidth_cast_lanes,←Nat.mul_assoc];exact safe)
  ∃ out : Memory W, Post a P rem Y table.records (2^w) cut source input origin out ∧
    ∃ (suffix : List Bool) (path : D.run.ArchivePath z.1 C O) (mid : Memory W) (count : D.roots z.1=N),
      D.run.plan.read (GridNativeDispatch.actualTable D safe).codes (List.ofFn (fun j : Fin cut=>source j.val))=
        some (z.1,suffix) ∧ D.run.FinalNumbered z.1 C O path ∧ out=TerminalWireArchive.image x mid ∧
      (∀ (U : Type) (L : (X).Words U),D.run.WordVisits (RecordedWordStep (a).K ((a).control:Word W)
        (((a).control+1:ℕ):Word W) (stop).header (stop).heap mid U (B).publicTemplate) z.1
        (Physical.registerOnLanes B U D.passes rem X splitLanes).1.steps L C O path) ∧
      let idx:=Resources.indexEquiv D.run z.1 count
      Resources.Registered destAddr dst par (fun j=>idx (D.run.plan.destination z.1 (initialLane (Nat.succ_pos axes) j)))
        (fun f=>units*D.run.chargeAt z.1 C start (idx.symm f)) after ∧
      (∀ i,i<(a).seed → after i=input i) ∧ (∀ i,i<hdr → after i=out i) ∧
      ∃ saved : Memory W,(O).Charged (node).banks (natural saved) start pairs ∧
        D.run.ArchiveRowsStored (node).banks (natural saved) z.1 C O path ∧
        (∀ i,TickWorkspace.base u 43 ≤ i → i<TickWorkspace.base u 45 → after i=saved i) ∧
        TraceRecovery.stagePost (a).K ss (a).cursor (O).layer (·<hdr) (natural out)
          (directoryCap B) (directoryCap B) (fun _=>False)
          (D.run.archiveList z.1 C O path (a).seedData) (D.run.finalArchive z.1 C O path).1 ∧
        MountedAt (natural out) (a).K ss (a).cursor ∧
        (∀ i,(a).initialRecords ≤ i → i<(a).metadataEnd → mid i=origin i) ∧
        ReceiverCache u (a).cursor.header (ss).length (rowBudget W node ((axes+1)*2^(axes+1)))
          (stop).heap node (O).layer (D.run.archiveList z.1 C O path (a).seedData) mid out saved after

/-- Registering the selected history and electing the true tick keep both
intermediate memories, so every later cached row has its original provenance. -/
theorem elect_histories (geom : ElectionRoom D l) (safe : GridNativeDispatch.WordRoom D)
    (z : D.trace) (sel : Fin (cap+1)→Bool) (t : Fin T)
    (textFit : text≤w^2) (self : Fin (w^2)→Bool) (ps : Fin args→Word W)
    (input origin : Memory W)
    (low : 2+(GridReceiverHeader.header text textFit self (t.val:Word W) ps sel).length≤(a).seed)
    (stored : let head:=GridReceiverHeader.header text textFit self (t.val:Word W) ps sel
      ∀ j : Fin head.length,input (2+j.val)=((head[j.val]).toNat:Word W))
    (navigation : (nav).Spec (·=input) (fun _=>Histories D l z sel safe input origin) (histTime+2*cut)) :
    let cost:=D.costs (GridNativeImage.resources D l) z.1 l.dimension l.sideMinusOne l.bank C units
    ((nav).seq choose).Spec (·=input) (fun _ out=>∃ reg,Histories D l z sel safe input origin reg ∧
      ∃ classified,GridSimulation.Assigned geom.teams_pos cost reg classified ∧
        GridReceiverTickDirectory.Ticked (GridReceiverTickDirectory.banks w u)
          (FactorAllocation.factors w cost (List.finRange (D.roots z.1)) t)
          (t.val:Word W) classified out)
      (histTime+2*cut+(GridSimulation.assignTime w N d+
        GridReceiverTickDirectory.clock W (((20*(w+1)+2)^d)*N))) := by
  intro cost
  let R:=Histories D l z sel safe input origin
  let result:=fun (reg out : Memory W) => ∃ classified,GridSimulation.Assigned geom.teams_pos cost reg classified ∧
    GridReceiverTickDirectory.Ticked (GridReceiverTickDirectory.banks w u)
      (FactorAllocation.factors w cost (List.finRange (D.roots z.1)) t) (t.val:Word W) classified out
  have select : (choose).Spec R result
      (GridSimulation.assignTime w N d+GridReceiverTickDirectory.clock W (((20*(w+1)+2)^d)*N)) := by
    intro p r s M loc regs slots exit rom pub cfg reg entry witness
    obtain ⟨_,_,_,_,_,cnt,_,_,_,_,registered,frame,_⟩:=witness
    have run:=elect D l geom z.1 cnt reg registered t textFit self ps sel (by
      intro header j
      rw [frame (2+j.val) ((Nat.add_lt_add_left j.isLt 2).trans_le low)]
      exact stored j) M
    exact run loc regs slots exit rom pub cfg reg entry rfl
  intro names registers sites machine
  exact Procedure.Spec.seq («A»:=nav) («B»:=choose) (pre:=(·=input)) (mid:=R)
    (left:=fun _ => R) (right:=result) navigation select (fun _ _ h => h) machine

/-- The two native procedures in the literal source prefix, preceding the
per-node compilation and terminal product. -/
def prefixProgram := (nav).seq choose

def prefixTime := histTime+2*cut+(GridSimulation.assignTime w N d+
  GridReceiverTickDirectory.clock W (((20*(w+1)+2)^d)*N))

def InputWindow (z : D.trace) (safe : GridNativeDispatch.WordRoom D)
    (room : GridSelector.Room D.run.plan (GridNativeDispatch.actualTable D safe).codes bits cap) :=
  GridSelector.encode D.run.plan (GridNativeDispatch.actualTable D safe).codes bits cap room (some z)

def coefficientInputs (stageRate rootRate degree coeff exp : ℕ) : Prop :=
  4+(P).length≤coeff*(w+1)^exp ∧
  setupPrice (P).length stageRate≤coeff*(w+1)^exp ∧ mapPrice degree rootRate≤coeff*(w+1)^exp

def Elected (geom : ElectionRoom D l) (safe : GridNativeDispatch.WordRoom D)
    (z : D.trace) (sel : Fin (cap+1)→Bool) (t : Fin T) (input origin out : Memory W) : Prop :=
  let cost:=D.costs (GridNativeImage.resources D l) z.1 l.dimension l.sideMinusOne l.bank C units
  ∃ reg,Histories D l z sel safe input origin reg ∧
    ∃ classified,GridSimulation.Assigned geom.teams_pos cost reg classified ∧
      GridReceiverTickDirectory.Ticked (GridReceiverTickDirectory.banks w u)
       (FactorAllocation.factors w cost (List.finRange (D.roots z.1)) t) (t.val:Word W) classified out

def shifted (l : GridNativeImage.Layout) (w : ℕ) (input : ℕ→Bool) : Memory (64*w) :=
  TickMountedPins.memory (w:=64*w) (fun i : Fin l.pinWidth=>input i.val)

def original (sel : Fin (cap+1)→Bool) (input : ℕ→Bool) :=
  TraceSeedWriter.memory a ss edges [] (GridStructuralHeader.selectorBit cap sel) (shifted l w input) D.passes

end

set_option maxHeartbeats 1600000 in
/-- The prefix starts on the shifted bit tape. Both archive scans read the
full installed numerical table and the same selector that specified this physical summand. -/
theorem selected_prefix (blk : Block F) {uN blocks : ℕ→ℕ} (scale : Scale uN blocks) (coef exp : ℕ) :
    ∀ᶠ w : ℕ in atTop,∀ {pc regs words size base fuel axes rr : ℕ} (hk : 2≤axes+1)
      (_axis : axes+1=uN w+1-w/2) (_hp : pc≤64*w) (_hr : regs≤64*w) (_hw : words≤64*w)
      (M : Machine (64*w) pc regs words) (fit : NativeTrace.Fits M size base ((axes+1)+w/2) fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (reps : blk.blockCharge*blocks w≤axes+1),
      let D : RunData F (64*w) pc regs words size base fuel axes (w/2):=
        ⟨M,fit,hF,st,blk,hk,blocks w,reps⟩
      ∀ (l : GridNativeImage.Layout) (geom : ElectionRoom D l) (safe : GridNativeDispatch.WordRoom D)
        (z : D.trace) (room : GridSelector.Room D.run.plan (GridNativeDispatch.actualTable D safe).codes
          (GridPhysicalSelector.bits D.run) l.selectorCap)
        (t : Fin ((l.sideMinusOne+1)^(l.dimension+1)*l.copies)) (recv : Machine (64*w) pc rr words)
        (txt : SelfAdvice.textSize (64*w) pc words≤w^2) (self : Fin (w^2)→Bool) (input : ℕ→Bool),
        let sel:=InputWindow D l z safe room
        let ps:=GridStructuralHeader.parameters blk (axes+1) (blocks w) l.selectorCap M fit hF st 0 (26*GridDescription.sector w)
        let head:=GridReceiverHeader.header _ txt self (t.val:Word (64*w)) ps sel
        let a:=archive D l
        let pinMem:=shifted l w input
        coefficientInputs D l.stageRate l.rootRate l.degree coef exp →
        l.dimension+1≤w → 2*((l.dimension+1)*GridIdleLayout.each l.dimension l.sideMinusOne l.bank)≤ size →
        2^(3*w/5)≤l.selectorCap → (1+6*pc+words)*(64*w)≤l.pinWidth →
        (∀ i,input i.val=NativeTrace.executable recv i) → 2+l.pinWidth+l.pinWidth<2^(64*w) →
        head.length≤l.pinWidth → 2+head.length≤a.seed →
        TraceFactorReceiver.Selector.headerReads _ txt self (t.val:Word (64*w)) ps sel input →
        (prefixProgram D l).Spec (·=pinMem) (fun _=>Elected D l geom safe z sel t pinMem (original D l sel input))
          (prefixTime D l) := by
  let rate:=3*5*10^26*65^14
  filter_upwards [TraceCompactSeed.eventual_resources blk scale rate 15,
    eventual_native_port_count (F:=F) scale,native_machine_controller blk scale,
    eventual_record_length blk scale,TraceFactorReceiver.publish blk scale coef exp,eventually_ge_atTop (64^10)]
    with w material ports controller length publication age
  intro pc regs words size base fuel axes rr hk _axis _hp _hr _hw M fit hF st reps D l geom safe z room
    t recv txt self input sel ps head a pinMem rates directions exterior cutFits programSpace honest pinSpace padded headLow raw
  let rad:=(axes+1)+w/2
  let G:=TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs words rad
  let off:=1+(rad+rad)
  let P:=blk.repeat (blocks w)
  let rem:=axes+1-P.charge
  let ss:=P.directory rem (axes+1)
  let edges:=P.finalEdges rem (axes+1)
  let src:=GridStructuralHeader.selectorBit l.selectorCap sel
  let origin:=original D l sel input
  let W:=64*w
  let cut:=2^(3*w/5)
  let V:=receiverAge w
  let beta:=GridStructuralHeader.recipientBase w
  have ageBounds:=receiverAge_chart w age
  have wp:=geom.pos
  have atTop:=TraceCompactSeed.recipient_top wp ageBounds.1 ageBounds.2
  have address:=TraceCompactSeed.archive_placement blk w beta (axes+1) off G.cells l.selectorCap a.rawStatic a.phase
  have small : a.phase+1+l.selectorCap≤beta := by
    rw [GridReceiverHeader.length] at headLow
    change 2+SelfAdvice.textSize W pc words+(GridNativeImage.parameterCount D l+1)*W+
      GridReceiverHeader.count w*W+1+l.selectorCap≤beta
    change 2+(SelfAdvice.textSize W pc words+((GridNativeImage.parameterCount D l+1)*W+
      (GridReceiverHeader.count w*W+(l.selectorCap+1))))≤beta at headLow
    omega
  obtain ⟨seed,limits,terminal,seedClock⟩:=material beta axes off G.cells l.selectorCap a.rawStatic a.phase
    reps _axis (ports _hp _hr _hw _axis M fit hF st) small atTop
  have coded : (stageCounts blk (blocks w) (axes+1)).sum*blk.alphabetCap*W≤cut := by
    rw [_axis]
    exact length (_axis ▸ reps)
  have hist : W*a.histWords ss≤cut := by
    simpa only [a,archive,TraceCompactSeed.archive,Archive.histWords,stageCounts,ss,P,rem,
      Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using coded
  obtain ⟨wordFit,executed,_⟩:=TraceFactorReceiver.admit (off:=off) (slots:=G.cells)
    blk hk reps M fit hF st 0 (26*GridDescription.sector w) txt self (t.val:Word W) sel input
    padded raw recv programSpace honest pinSpace headLow hist cutFits seed limits terminal seedClock
    (controller _hp _hr _hw hk _axis M fit hF st reps)
  let ct:=GridNativeDispatch.actualTable D safe
  have flag : sel 0=true:=rfl
  have decoded:=GridSelector.decode_encode D.run.plan ct.codes (GridPhysicalSelector.bits D.run) l.selectorCap room (some z)
  have full : GridSelector.read D.run.plan ct.codes (GridPhysicalSelector.bits D.run) l.selectorCap
      (List.ofFn (Fin.tail sel))=some z := by
    change GridSelector.decode D.run.plan ct.codes (GridPhysicalSelector.bits D.run) l.selectorCap sel=some (some z) at decoded
    simp only [GridSelector.decode,flag,ite_true] at decoded
    obtain ⟨history, parsed, selected⟩ := Option.map_eq_some_iff.mp decoded
    exact parsed.trans (congrArg some (Option.some.inj selected))
  have accepted : (GridSelector.read D.run.plan ct.codes (GridPhysicalSelector.bits D.run) l.selectorCap
      (List.ofFn (Fin.tail sel))).isSome := by rw [full];rfl
  rcases rates with ⟨dep,setup,maps⟩
  have navigation : (TraceReceiverProgram.navigation blk W (native D l)).Spec (·=pinMem)
      (fun _=>Histories D l z sel safe pinMem origin) (cut+(cut+Archive.terminalTime (a.terminal ss edges W))+2*cut) := by
    intro labels registers slots machine pcMap regMap pubMap exit installed rom cfg m start same
    obtain ⟨n, hn, cfg', after, ran, finished, out, post, h, tail, path, mid, count, parsed, body⟩ :=
      publication ageBounds.1 ageBounds.2 hk _axis _hp _hr _hw M fit hF st reps a address rfl rfl rfl rfl
        (l.dimension+1) (GridIdleLayout.each l.dimension l.sideMinusOne l.bank) (4+P.length)
        (setupPrice P.length l.stageRate) (mapPrice l.degree l.rootRate) directions
        ((Nat.le_mul_of_pos_left _ (Nat.succ_pos l.dimension)).trans
          ((Nat.le_mul_of_pos_left _ (by decide : 0 < 2)).trans exterior)) exterior dep setup maps src pinMem origin
        rfl safe _ _ executed accepted machine pcMap regMap pubMap exit installed rom cfg m start same
    have equal:=selected_registered D l safe room z sel rfl cutFits coded h tail parsed
    subst h
    exact ⟨n, hn, cfg', after, ran, finished, out, post, tail, path, mid, count, parsed, body⟩
  have stored : ∀ j : Fin head.length, pinMem (2+j.val) = ((head[j.val]).toNat : Word W) := by
    intro j
    let i : Fin l.pinWidth := ⟨j.val,j.isLt.trans_le padded⟩
    have cell : pinMem (2+j.val) = BitLayout.bitWord W (input j.val) :=
      TickMountedPins.memory_at (w:=W) (fun k : Fin l.pinWidth => input k.val) i
    have digit : input j.val = head[j.val] := raw j
    rw [cell, digit]
    cases head[j.val] <;> rfl
  intro labels registers slots machine
  exact elect_histories D l geom safe z sel t txt self ps pinMem origin headLow stored navigation machine

end Hierarchy.GridReceiverDirectory
end

end OAI
