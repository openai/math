import OAI.Hierarchy.GridNativeImage
import OAI.Hierarchy.GridDispatchFlag
import OAI.Hierarchy.GridWriterSpace
import OAI.Hierarchy.GridCompilerAdmission

namespace OAI
/-! # The one selector setting for the physical grid emitter
Every admitted flag is its selected trace's unique encoding. Therefore all
accepted inputs, including inputs with different exterior bits, use the
same tick headers, data addresses, and chronological work assignment.
-/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.GridNativeDispatch
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.PhysicalProcedure RAM.TickStageSpec Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution TraceAdmission TraceNodeHeaders NodePublication GridThrough UniversalGrid
open GridRegisteredSetting GridNativeImage TraceFactorReceiver.Gather Computability.VPVNP Computability.VPVNP.RAMMemory Filter
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {w pc regs slots S base fuel axes : ℕ}
variable (D : RunData F (64*w) pc regs slots S base fuel axes (w/2)) (l : GridNativeImage.Layout)
local notation "m" => l.dimension
local notation "n" => l.sideMinusOne
local notation "B" => l.bank
local notation "q" => l.copies
local notation "d" => l.pinWidth
local notation "cap" => l.selectorCap
local notation "W" => (64*w)
local notation "J" => GridDescription.sector w
local notation "rails" => GridControllerSimGeometry.railCount m n B
local notation "dir" => GridIdleLayout.direction («m»:=m) («n»:=n) («B»:=B)
local notation "shape" => GridControllerIdle.shape m n B l.logRadix q d l.receiverPC
local notation "enc" => FieldCode.ofCardLe D.field
local notation "unit" => D.issuedUnit w l.degree l.stageRate l.rootRate
local notation "depth" => ((axes+1)+w/2)
local notation "G" => TraceStaticRow.gateTable D.field D.fit.width D.fit.labels base fuel D.state regs slots depth
local notation "off" => (1+(depth+depth))
local notation "stages" => (D.block.repeat D.passes).length
local notation "ss" => (D.block.repeat D.passes).directory (axes+1-(D.block.repeat D.passes).charge) (axes+1)
local notation "last" => TraceRecovery.lastLayer (archive D l).K ss (archive D l).cursor (archive D l).seedLayer
local notation "ar" => GridCompilerAdmission.arena w
local notation "bits" => GridPhysicalSelector.bits D.run

abbrev WordRoom := D.block.repeatFactor*((D.block.cursorState D.axesFit (w/2) off (G).cells).maxWidth+1)*
  D.block.widthBase^D.passes < 2^W

abbrev Tables := PhysicalStage.Program.RecordTable D.run D.block.alphabetCap W
  (stageCounts D.block D.passes (axes+1))

def actualTable (safe : WordRoom D) : Tables D :=
  physicalTable D.block D.axesFit (w/2) off (G).cells D.passes W D.passesFit safe

theorem selectorRoom (source : Tables D) (fits : GridSelector.Room D.run.plan source.codes bits cap)
    (safe : WordRoom D) : GridSelector.Room D.run.plan (actualTable D safe).codes bits cap := by
  intro z
  simpa only [(actualTable D safe).write_size,source.write_size] using fits z

variable {rc kc : ℕ} (X : Catalyst.Approximation F (l.dimension+1) (l.copies*l.pinWidth))
variable (recv : Machine (64*w) l.receiverPC rc kc) (raw gateBase : ℕ)
variable (textFits : l.receiverText ≤ w^2)
def params := GridStructuralHeader.parameters D.block (axes+1) D.passes cap
  D.machine D.fit D.field D.state raw gateBase

local notation "par" => params D l raw gateBase
local notation "header" => GridRegisteredPublication.headers («m»:=m) («n»:=n) («q»:=q) D par recv
local notation "advice" => GridPinCapturedSources.advice (S:=S) (e:=rails) (compact:=B) X enc par recv D.machine

abbrev Rooms := ∀ (s : Fin (cap+1) → Bool) (z : D.trace),
  D.Room z.1 D.issuedCharges unit w m n B q d (header s textFits)

variable (rooms : Rooms D l recv raw gateBase textFits)
variable (reserved : ∀ j,X.width j ≤ l.bank) (accepts : 0 < l.receiverPC)

def setting (C : D.run.plan.Codes) (room : GridSelector.Room D.run.plan C bits cap) :
    Option D.trace → GridThrough.Setting X n rails dir :=
  let flag := GridSelector.encode D.run.plan C bits cap room
  D.dispatch (receiverRegs:=rc) (receiverWords:=kc) (resources D l) D.issuedCharges unit accepts X reserved
    (fun z => header (flag (some z)) textFits) (fun _ => advice) (fun z => rooms _ z)

def source := GridSelfHeader.suffix («B»:=B) X enc par

local notation "bytes" => GridDescription.code («q»:=w^2) recv D.machine
local notation "chosen" => setting D l X recv raw gateBase textFits rooms reserved accepts
local notation "control" => GridThrough.honestController D.run.plan
local notation "image" => GridNativeImage.emitter D l
local notation "time" => GridNativeImage.emissionTime D l

private abbrev inputLaneCount (_ : RunData F (64*w) pc regs slots S base fuel axes (w/2)) :=
  2^(axes+1)

/-- Static bounds consumed by the issuer. The dimensions and all page lengths
are available before the native machine reads the external pins or flag. -/
structure Fits (coef exponent : ℕ) : Prop where
  axes : m+1 ≤ w
  cut : 2^(3*w/5) ≤ cap
  bank : 0 < B
  pins : 0 < q*d
  capFit : cap < J
  rawExtent : GridSelfHeader.rawSize w rails B (parameterCount D l) ≤ 2^(4*w)
  actualSize : S=GridSelfHeader.rawSize w rails B (parameterCount D l)
  degree : 4+stages ≤ coef*(w+1)^exponent
  setup : setupPrice stages l.stageRate ≤ coef*(w+1)^exponent
  maps : mapPrice l.degree l.rootRate ≤ coef*(w+1)^exponent
  small : GridPinArena.Small w (GridPinPublisher.canonical w (m+1) n q d (parameterCount D l)
    (cap+1) l.receiverText B rails S (last).count (ss).length (inputLaneCount D) (2*2^(w/2)))
    S (inputLaneCount D) ((ss).length*(inputLaneCount D)) ((20*(w+1)+2)^((m+1)+2))
  idle : GridControllerIdle.Fits W ar shape
  geometry : GridControllerIdle.Room ar shape
  space : GridCompilerAdmission.Space X w n rails B

/-- This is exactly the native write clause for the honest controller whose
description is the receiver followed by the actual self-installed machine.
The physical record table is fixed before either input function is supplied. -/
def Writes (C : D.run.plan.Codes) (room : GridSelector.Room D.run.plan C bits cap) : Prop :=
  ∀ (x : GridDiagonal.Pins (Fin rails)) (s : Bits (cap+1)),
    let selected := control C bits (chosen C room) bytes bytes s
    let pin := x ∘ Wiring.railPin.symm
    let tape := GridDescription.input pin bytes (source D l X raw gateBase)
    Admission enc (image).block (image).publicData
      (·=GuessLoop.install (12*J) s (initialMemory S (fun i => TraceBitHeader.binaryWord W (tape i))))
      (fun _ => selected.isSome) (fun _ out => ∀ v,selected=some v →
        ∀ i < BitLayout.footprint (GridNativeEvaluator.net X v.1),
          out i=BitLayout.memory (GridNativeEvaluator.net X v.1) enc pin (fun _=>false) i) time

def simulationTime :=
  let stageEdges := (D.block.repeat D.passes).finalEdges (axes+1-(D.block.repeat D.passes).charge) (axes+1)
  GridEvaluatorBudget.sim w m n q B d rails cap (parameterCount D l) l.receiverText S
    (last).count (ss).length (2^(axes+1)) (2*2^(w/2)) l.logRadix l.receiverPC (archive D l) ss stageEdges ar

local notation "capture" => GridPinPublisher.capture (compact:=B) X enc par recv D.machine
local notation "loaded" => GridApproximationAdvice.paddedMemory X enc B (2*J)

def Runs : Prop := ∀ (pin : Fin (rails*2) → Bool) (s : Bits (cap+1)),
  ∃ safe : WordRoom D,
    let C := (actualTable D safe).codes
    let selected := GridSelector.read D.run.plan C bits cap (List.ofFn (Fin.tail s))
    s 0=true →
    Admission enc (simulated D l).block (simulated D l).publicData (·=loaded (capture pin s))
      (fun _ => selected.isSome) (fun _ out => ∀ z, selected=some z → GridOrderedSources.Raw X
        (D.scheduled (resources D l) z.1 D.issuedCharges unit (header s textFits) advice (rooms s z) X reserved).1
        enc ar B pin out (loaded (capture pin s))) (simulationTime D l)

theorem write_of_runs {coef exponent : ℕ} (geom : Fits D l X coef exponent) (large : 768 ≤ w)
    (other : Tables D) (tables : GridSelector.Room D.run.plan other.codes bits cap)
    (native : Runs D l X recv raw gateBase textFits rooms reserved) :
    ∃ safe : WordRoom D, Writes D l X recv raw gateBase textFits rooms reserved accepts
      (actualTable D safe).codes (selectorRoom D l other tables safe) := by
  obtain ⟨safe,_⟩ := native (fun _ => false) (fun _ => false)
  let C := (actualTable D safe).codes
  let canon := selectorRoom D l other tables safe
  let Q := chosen C canon
  refine ⟨safe,?_⟩
  intro x s
  let pin := x ∘ Wiring.railPin.symm
  let selected := GridSelector.decode D.run.plan C bits cap s
  let programs := selected.map (fun z => (Q z).1)
  have proj : (fun z : Option D.trace => z.elim ((Q none).1) (fun a => (Q (some a)).1)) =
      (fun z => (Q z).1) := by funext z; cases z <;> rfl
  have upper : 64*J < 2^W := GridDescription.sectors_fit (by omega)
  have small : GridSelfHeader.rawSize w rails B (parameterCount D l) ≤ 12*J := by
    have start := GridDescription.small_before_sector (by omega : 0 < w)
    have bytesFit := geom.rawExtent
    change 2^(4*w) < J at start
    omega
  have runDispatch {targetPC targetRegisters targetSlots : ℕ} (target : Machine W targetPC targetRegisters targetSlots) := GridCompilerAdmission.dispatch (rc:=rc) (kc:=kc) (logRadix:=l.logRadix)
    enc par recv D.machine X accepts reserved D.run.plan C bits pin s (fun z => (Q (some z)).1)
    (simulated D l) (simulationTime D l) geom.idle geom.geometry geom.space.words geom.space.compact
    geom.capFit (by change 13*J+3 < 2^W; have : 0 < J := Nat.two_pow_pos _; omega) small (by
      intro flag cpu registers slots machine pc reg pub exit installed values cfg mem entered before
      obtain ⟨_,check⟩ := native pin s
      obtain ⟨accepted,rejected⟩ := check flag machine pc reg pub exit installed values cfg mem entered before
      constructor
      · intro valid
        obtain ⟨ticks,bound,result,out,atExit,rawOutput,ran⟩ := accepted valid
        refine ⟨ticks,bound,result,out,atExit,?_,ran⟩
        intro z eqn
        have encoded := GridDispatchFlag.true_encode D.run.plan C bits cap canon s flag eqn
        let issued (sel : Bits (cap+1)) := (D.scheduled (resources D l) z.1 D.issuedCharges unit
          (header sel textFits) advice (rooms sel z) X reserved).1
        have original : GridOrderedSources.Raw X (issued s) enc ar B pin out (loaded (capture pin s)) :=
          rawOutput z eqn
        change GridOrderedSources.Raw X (issued (GridSelector.encode D.run.plan C bits cap canon (some z)))
          enc ar B pin out (loaded (capture pin s))
        exact (congrArg (fun flagBits => GridOrderedSources.Raw X (issued flagBits) enc ar B pin out
          (loaded (capture pin s))) encoded).mpr original
      · exact rejected) target
  have nav : Admission enc (dispatch D l).block (dispatch D l).publicData (·=loaded (capture pin s))
      (fun _=>programs.isSome) (fun _ out => ∀ v,programs=some v → GridOrderedSources.Raw X v enc ar B pin out
        (loaded (capture pin s))) (navigationTime D l) := by
    have programs_eq : programs = selected.map (fun z : Option D.trace =>
        z.elim ((Q none).1) (fun a => (Q (some a)).1)) :=
      congrArg (fun choose => selected.map choose) proj.symm
    rw [programs_eq]
    intro nPC nRegs nSlots target
    exact runDispatch target
  have first (z : Option D.trace) : (Q z).1.pass=GridLens.firstPassage (Q z).1.direction
      (Q z).1.row (Q z).1.touch X.width (Q z).1.untouched_capacity := by
    cases z <;> rfl
  have ready {targetPC targetRegisters targetSlots : ℕ} (target : Machine W targetPC targetRegisters targetSlots) := GridCompilerAdmission.admission (start:=12*J) (limit:=GridNativeImage.limit F l)
    X enc par recv D.machine x s (dispatch D l) (navigationTime D l) programs large geom.bank geom.rawExtent
    small geom.space.writer geom.space.selection (fun v _ => geom.space.image v) geom.space.words
    (by intro v hit; obtain ⟨z,_,ev⟩ := Option.map_eq_some_iff.mp hit; subst v; exact first z) nav target
  have lift {targetPC targetRegisters targetSlots : ℕ} (target : Machine W targetPC targetRegisters targetSlots) := GridDispatchFlag.typed_write D.run.plan C bits cap X dir Q bytes s enc image
    (·=capture pin s) pin time (@ready) target
  let boot (size : ℕ) := GuessLoop.install (12*J) s (initialMemory size (fun i =>
    TraceBitHeader.binaryWord W (GridDescription.input pin bytes (source D l X raw gateBase) i)))
  change Admission enc (image).block (image).publicData _ _ _ time
  intro nPC nRegs nSlots target pcMap regMap pubMap exit installed values cfg mem entered initial
  apply lift target pcMap regMap pubMap exit installed values cfg mem entered
  change mem = boot S at initial
  change mem = boot (GridSelfHeader.rawSize w rails B (parameterCount D l))
  exact initial.trans (congrArg boot geom.actualSize)

/-- The fixed emitter supplies the native-distribution write clause at every
sufficiently large width of the physical block schedule. -/
theorem native_write (blk : Block F) {u reps : ℕ → ℕ} (scale : Scale u reps) (coef exponent : ℕ) :
    ∀ᶠ age : ℕ in atTop, ∀ {cpu rr pp size mount ticks ax : ℕ}
      (info : RunData F (64*age) cpu rr pp size mount ticks ax (age/2)),
      info.block=blk → info.passes=reps age → ax+1=u age+1-age/2 →
      cpu ≤ 64*age → rr ≤ 64*age → pp ≤ 64*age →
      ∀ (layout : GridNativeImage.Layout) {rr' pp' : ℕ}
        (cat : Catalyst.Approximation F (layout.dimension+1) (layout.copies*layout.pinWidth))
        (receiver : Machine (64*age) layout.receiverPC rr' pp') (codeBase gateTable : ℕ)
        (storedText : layout.receiverText ≤ age^2)
        (budget : Rooms info layout receiver codeBase gateTable storedText)
        (width : ∀ j,cat.width j ≤ layout.bank) (entry : 0 < layout.receiverPC)
        (_numbers : Fits info layout cat coef exponent) (codec : Tables info)
        (fitting : GridSelector.Room info.run.plan codec.codes (GridPhysicalSelector.bits info.run) layout.selectorCap),
      ∃ safe : WordRoom info, Writes info layout cat receiver codeBase gateTable storedText budget width entry
        (actualTable info safe).codes (selectorRoom info layout codec fitting safe) := by
  filter_upwards [GridNativeController.simulate blk scale coef exponent,eventually_ge_atTop 768] with age execute old
  intro cpu rr pp size mount ticks ax info actualBlock actualPasses axis cpuFit rrFit ppFit
  obtain ⟨machine,fit,hF,state,owner,axFit,passes,passFit⟩ := info
  change owner=blk at actualBlock
  change passes=reps age at actualPasses
  subst owner
  subst passes
  let info : RunData F (64*age) cpu rr pp size mount ticks ax (age/2) :=
    ⟨machine,fit,hF,state,blk,axFit,reps age,passFit⟩
  intro layout rr' pp' cat receiver codeBase gateTable storedText budget width entry _numbers codec fitting
  apply write_of_runs info layout cat receiver codeBase gateTable storedText budget width entry _numbers old codec fitting
  intro pin s
  have space := _numbers.space
  let stages' := (blk.repeat (reps age)).length
  have packed := space.compact
  have smallRaw := _numbers.rawExtent.trans (GridDescription.small_before_sector (by omega : 0 < age)).le
  obtain ⟨safe,works⟩ := execute axFit axis cpuFit rrFit ppFit machine fit hF state passFit
    (logRadix:=layout.logRadix) cat width receiver codeBase gateTable pin s storedText _numbers.axes _numbers.cut
    (4+stages') (setupPrice stages' layout.stageRate) (mapPrice layout.degree layout.rootRate)
    _numbers.degree _numbers.setup _numbers.maps smallRaw packed _numbers.capFit.le _numbers.pins
    _numbers.actualSize.ge _numbers.small _numbers.idle _numbers.geometry space.writer
  refine ⟨safe,?_⟩
  intro fixedCodes selectedTrace live
  have clockEq :
      let last' := TraceRecovery.lastLayer (archive info layout).K
        ((info.block.repeat info.passes).directory (ax+1-(info.block.repeat info.passes).charge) (ax+1))
        (archive info layout).cursor (archive info layout).seedLayer
      let ss' := (info.block.repeat info.passes).directory (ax+1-(info.block.repeat info.passes).charge) (ax+1)
      let edges := (info.block.repeat info.passes).finalEdges (ax+1-(info.block.repeat info.passes).charge) (ax+1)
      let K := 2^(3*age/5)
      (K+(K+Archive.terminalTime ((archive info layout).terminal ss' edges (64*age))))+
        (2*K+GridRegisteredPublication.clock age layout.dimension layout.sideMinusOne layout.bank layout.copies
          layout.pinWidth (parameterCount info layout) (layout.selectorCap+1) layout.receiverText size last'.count
          ss'.length (2^(ax+1)) (2^(age/2)) layout.logRadix layout.receiverPC)=simulationTime info layout := by
    simp only [simulationTime,GridEvaluatorBudget.sim,GridRegisteredPublication.clock,
      Nat.add_assoc]
  rw [←clockEq]
  intro targetPC targetRegisters targetSlots target maps registers publics exit installed data cfg mem atEntry input
  exact works (budget s) live target maps registers publics exit installed data cfg mem atEntry input

end Hierarchy.GridNativeDispatch
end

end OAI
