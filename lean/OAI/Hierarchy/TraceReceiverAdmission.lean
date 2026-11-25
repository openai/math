import OAI.Hierarchy.TraceCompactSeed
import OAI.Hierarchy.TraceReceiverSelectorWindow
import OAI.Hierarchy.GridPhysicalAdmission

namespace OAI
/-! # Actual relocated journal of a receiver tick, from its own native pin tape -/

namespace Hierarchy.TraceFactorReceiver
open ThreeFlat Diagonal Diagonal.PhysicalStage RAM RAM.PhysicalProcedure RAM.TickStageSpec
open NavigationPass NavigationDirectory TraceDistribution TraceAdmission Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
/-- A successful parse executes the native admission block to its actual returned
memory. This form feeds a deterministic continuation such as S43/S44 registration. -/
theorem positive {F : Type*} [Semiring F] {W budget : ℕ} (field : FieldCode F W)
    (proc : Procedure W) {pre valid : Memory W → Prop} {post : Memory W → Memory W → Prop}
    (admission : Admission field proc.block proc.publicData pre valid post budget)
    (accept : ∀ m, pre m → valid m) : proc.Spec pre post budget := by
  intro pc regs k M P R pub exit rom data c m start hm
  obtain ⟨t,cost,d,image,pcEnd,body,adv⟩ :=
    (admission M P R pub exit rom data c m start hm).1 (accept m hm)
  exact ⟨t,cost,d,image,adv,pcEnd,body⟩

variable {F : Type} [Field F] [Fintype F] {w pc regs words S base fuel d : ℕ}
variable (B : Block F) {k n off slots cap : ℕ} (hk : 2≤k+1) (fitStages : B.blockCharge*n≤k+1)
    (M : Machine (64*w) pc regs words) (fit : NativeTrace.Fits M S base d fuel)
    (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (raw gateBase : ℕ)
set_option quotPrecheck false
local notation "W" => 64*w
local notation "G" => TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs words d
local notation "ed" => GridStructuralHeader.directory (w:=w) B (k+1) n cap
local notation "tc" => TraceReceiverTemplate.count G
local notation "total" => GridStructuralHeader.wordCount (ed).length tc (RAM.HistoryStageBody.Physical.libraryWords B W)
local notation "text" => SelfAdvice.textSize W pc words
local notation "phase" => GridStructuralHeader.receiverPhase w text total
local notation "beta" => GridStructuralHeader.recipientBase w
local notation "beginDir" => 2+text+W*(1+(ed).length+tc)
local notation "params" => GridStructuralHeader.parameters B (k+1) n cap M fit hF st raw gateBase
local notation "arch" => TraceCompactSeed.archive B w beta (k+1) off slots cap beginDir phase
local notation "P" => B.repeat n
local notation "rem" => k+1-(P).charge
local notation "ss" => (P).directory rem (k+1)
local notation "edges" => (P).finalEdges rem (k+1)
local notation "cut" => 2^(3*w/5)
variable (textFit : SelfAdvice.textSize (64*w) pc words≤w^2) (self : Fin (w^2)→Bool)
    (index : Word (64*w)) (sel : Fin (cap+1)→Bool) {p : ℕ} (input : ℕ→Bool)
local notation "head" => GridReceiverHeader.header text textFit self index params sel
variable (padded : (GridReceiverHeader.header (w:=w) (SelfAdvice.textSize (64*w) pc words)
    textFit self index (GridStructuralHeader.parameters B (k+1) n cap M fit hF st raw gateBase) sel).length≤p)
    (stored : Selector.headerReads (SelfAdvice.textSize (64*w) pc words)
      textFit self index (GridStructuralHeader.parameters B (k+1) n cap M fit hF st raw gateBase) sel input)
local notation "pinMem" => TickMountedPins.memory (w:=W) (fun i : Fin p=>input i.val)
local notation "source" => GridStructuralHeader.selectorBit cap sel
local notation "origin" => TraceSeedWriter.memory (arch) ss edges [] source pinMem n
local notation "X" => B.cursorState hk (w/2) off slots
local notation "r" => Physical.run B hk (w/2) off slots n fitStages
local notation "field" => FieldCode.ofCardLe hF

include padded stored in
/-- The independent T computation executes its initial shuffle, then initializes and
runs all selected stages at its own archive addresses. On every valid selector the
actual final memory contains the native journal and terminal-width receipt. -/
theorem admit {rregs : ℕ} (recv : Machine W pc rregs words)
    (programRoom : (1+6*pc+words)*W≤p)
    (programBits : ∀ i,input i.val=NativeTrace.executable recv i)
    (pinRoom : 2+p+p<2^W)
    (headerRoom : 2+(head).length≤beta)
    (recordLength : W*(arch).histWords ss≤cut) (capacity : cut≤cap)
    (seed : TraceSeedWriter.Fits (arch) ss edges n k W)
    (limits : (arch).TraceLimits (2^w) ((arch).control:Word W) ss edges cut)
    (room : (arch).TerminalRoom ss edges W)
    (clock : (arch).bootTime ss edges W+(arch).seedTime+6≤cut)
    (controller : ControllerAt B w k n off slots hk fitStages) :
    let lanes : k+1=(P).charge+rem := by rw [B.charge_repeat];omega
    let A : State (2^B.exponent 0) ((P).charge+rem) := lanes ▸ X
    ∃ hw : B.repeatFactor*((X).maxWidth+1)*B.widthBase^n<2^W,
      let codes:=physicalTable B hk (w/2) off slots n W fitStages hw
      let internal:=B.recordTable B.alphabetCap W n rem A le_rfl
        (by rw [State.maxWidth_cast_lanes,←Nat.mul_assoc];exact hw)
      let stages:=GridPhysicalAdmission.program B (arch) ss edges W n
      let proc:=(TickHeaderShift.procedure W p).seq stages
      let valid : Memory W → Prop := fun _ =>(GridSelector.read (r).plan codes.codes (fun h=>((r).terminalLayer h).state.widthSum)
        cap (List.ofFn (fun j : Fin cap=>sel j.succ))).isSome
      let done:=fun _ out : Memory W=>GridPhysicalAdmission.Post (arch) (P) rem A internal.records
        (2^w) cut source pinMem origin out
      let fuel:=cut+(cut+Archive.terminalTime ((arch).terminal ss edges W))
      Admission field stages.block stages.publicData (·=pinMem) valid done fuel ∧
        Admission field proc.block proc.publicData (·=inputMemory recv p input) valid done ((28+16*p)+fuel) := by
  intro lanes A
  let a:=arch
  let cur : Word W:=a.control
  let ctr : Word W:=((a.control+1:ℕ):Word W)
  have placed:=TraceCompactSeed.archive_placement B w beta (k+1) off slots cap beginDir phase
  have bell : a.control+1<2^W := seed.space.counterFit
  have table : a.seed+(a.directory ss edges W).length<2^W := by
    apply limits.tables.trans_lt
    have baseBound := bell
    change beta+6*(2^w)^4+1<2^W at baseBound
    change beta+(2^w)^4<2^W
    omega
  have cp : cur.val=a.control:=Fin.val_cast_of_lt (by omega)
  have ct : ctr.val=a.control+1:=Fin.val_cast_of_lt bell
  obtain ⟨first,visit,counter,roots,foot,frame⟩ :=
    TraceCompactSeed.initialize B (k+1) n cap off slots M fit hF st raw gateBase textFit self index sel input
      padded stored hk rfl headerRoom (recordLength.trans capacity) seed limits room clock
  have pos : 1<2^W := by omega
  have extent : Selector.phase w total text+(cap+1)≤beta := by
    rw [GridReceiverHeader.length] at headerRoom
    dsimp only [Selector.phase,Selector.first]
    omega
  have addr : a.phase=Selector.phase w total text := by
    change GridStructuralHeader.receiverPhase w text total=_
    simp [GridStructuralHeader.receiverPhase,Selector.phase,Selector.first,Nat.add_assoc]
  have window : a.RawWindow ss source origin := by
    apply (Selector.window text textFit self index params sel input padded stored a ss origin addr
      (congrArg (·+1) addr) (congrArg (·+1) addr) rfl extent ?_).1
    intro i
    exact frame _ (Or.inl (by have := i.isLt; omega))
  obtain ⟨word,checked⟩ := GridSelector.controller_terminal B hk fitStages controller a beta cur ctr field
    placed cp (by omega) rfl source origin capacity recordLength table room window pos
  refine ⟨word,?_⟩
  intro codes internal stages proc valid done fuel
  let good : Memory W → Prop := fun _ => (GridSelector.read (r).plan codes.codes
    (fun h=>((r).terminalLayer h).state.widthSum) cap (List.ofFn (fun j : Fin cap=>sel j.succ))).isSome
  have card : Fintype.card A.Base=k+1 := (Program.baseCast lanes X).trans (Fintype.card_fin _)
  have staged : Admission field stages.block stages.publicData (·=pinMem) valid done fuel := by
    intro targetPC targetRegisters targetWords machine pcMap regMap pubMap exit code rom cfg mem entry initial
    obtain ⟨yes,no⟩ := admission_seq field (TraceSeedWriter.procedure a ss edges n)
      ((NavigationPass.repeated cur ctr a.K B).seq (TerminalWireArchive.program (a.terminal ss edges W)))
      (good:=good) (admission_of_spec field _ first) checked (fun _ _ _=>trivial)
      (by
        intro _ mid _ _ eq
        subst mid
        refine ⟨⟨rfl,visit,counter⟩,?_⟩
        have capacityEq : a.pairCapacity = cap := rfl
        have bitsEq : List.ofFn (fun j : Fin cap => source j.val) =
            List.ofFn (fun j : Fin cap => sel j.succ) := GridStructuralHeader.selector_body (cap:=cap) sel
        rw [capacityEq]
        change (GridSelector.read (r).plan codes.codes (fun h => ((r).terminalLayer h).state.widthSum)
          cap (List.ofFn (fun j : Fin cap => source j.val))).isSome = true ↔
            (GridSelector.read (r).plan codes.codes (fun h => ((r).terminalLayer h).state.widthSum)
              cap (List.ofFn (fun j : Fin cap => sel j.succ))).isSome = true
        rw [bitsEq])
      machine pcMap regMap pubMap exit code rom cfg mem entry initial
    refine ⟨fun live => ?_,no⟩
    obtain ⟨t,ht,last,out,returned,⟨mid,eq,saved⟩,steps⟩ := yes live
    subst mid
    refine ⟨t,ht,last,out,returned,?_,steps⟩
    refine ⟨?_,roots,foot,fun z hz=>frame z (.inl hz),?_⟩
    · simpa only [card] using visit.cast lanes
    simpa only [card] using saved
  refine ⟨staged,?_⟩
  intro targetPC targetRegisters targetWords machine pcMap regMap pubMap exit code rom cfg mem entry initial
  obtain ⟨yes,no⟩ := admission_seq field (TickHeaderShift.procedure W p) stages
    (good:=good) (admission_of_spec field _ (mount_input recv input programRoom programBits pinRoom))
    staged (fun _ _ _=>trivial)
    (fun _ mid _ _ eq=>⟨eq,Iff.rfl⟩)
    machine pcMap regMap pubMap exit code rom cfg mem entry initial
  refine ⟨fun live => ?_,no⟩
  obtain ⟨t,ht,last,out,returned,⟨mid,_,saved⟩,steps⟩ := yes live
  exact ⟨t,ht,last,out,returned,saved,steps⟩

end
end Hierarchy.TraceFactorReceiver

end OAI
