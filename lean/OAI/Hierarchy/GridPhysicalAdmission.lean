import OAI.Hierarchy.GridAdmissionRoom
import OAI.Hierarchy.GridSimulationHistories
import OAI.Hierarchy.GridStructuralCapture
import OAI.Hierarchy.TraceSeedVisit
import OAI.Hierarchy.GridTraceCap

namespace OAI
/-! # The physical program that admits exactly the grid's simulated histories -/

namespace Hierarchy.GridPhysicalAdmission
open ThreeFlat RAM Diagonal Diagonal.PhysicalStage NavigationPass NavigationDirectory
open TraceDistribution TraceAdmission RAM.PhysicalProcedure RAM.TickStageSpec Computability.VPVNP.BurstRAM PrivateRAM Filter
open scoped Classical
noncomputable section
open scoped Fin.CommRing


variable {F : Type} [Field F] [Fintype F] (B : Block F)

/-- Only the geometry at the chosen width enters the program. The selector,
the input tape and its selected terminal history are read at execution. -/
def program (a : Archive) (ss : List Stage) (edges W n : ℕ) : Procedure W :=
  (TraceSeedWriter.procedure a ss edges n).seq
    ((NavigationPass.repeated (a.control:Word W) ((a.control+1:ℕ):Word W) a.K B).seq
      (TerminalWireArchive.program (a.terminal ss edges W)))

/-- The semantic receipt retains both the initialized ancestor nodes and
the entire selected stage journal before terminal-width publication. -/
def Post {stages W : ℕ} (a : Archive) (P : Program F stages) (rem : ℕ)
    (X : State (2^stages) (P.charge+rem)) (E : (P.run rem X).Records)
    (limit cut : ℕ) (source : ℕ→Bool) (input origin out : Memory W) : Prop :=
  let ss:=P.directory rem (Fintype.card X.Base)
  let edges:=P.finalEdges rem (Fintype.card X.Base)
  let short:=List.ofFn (fun i : Fin cut=>source i.val)
  a.Visit ss edges source (a.control:Word W) [] X origin ∧
    a.seedData.Reads (fun z=>(origin z).val) ∧
    a.seedData.Footprint (fun z=>a.initialRecords≤z ∧ z<a.metadataEnd) (fun z=>(origin z).val) ∧
    (∀ z,z<a.seed→ origin z=input z) ∧
    ∃ mid,(a.TraceJournal limit (a.control:Word W) ((a.control+1:ℕ):Word W) P rem X a.cursor
      short origin mid ∧ ∃ v : Run.WireLayer,(P.run rem X).EndsAt E short v (short.drop (W*a.histWords ss))
      ∧ a.Visit ss edges source (a.control:Word W) ss v.state mid) ∧
      out=TerminalWireArchive.image (a.terminal ss edges W) mid

/-- Validation of the chosen physical compression on each actual RAM input
image, including deterministic initialization from directory and selector
bits, early malformed stages and the late padding rejection. -/
theorem admits {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {pc regs words k S base fuel : ℕ} (hk : 2≤k+1)
      (axes : k+1=u w+1-w/2) (hp : pc≤64*w) (hr : regs≤64*w) (hs : words≤64*w)
      (M : Machine (64*w) pc regs words) (fit : NativeTrace.Fits M S base ((k+1)+w/2) fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (fits : B.blockCharge*s w≤k+1)
      {g p E bank tp tr tk cap : ℕ} (X : Catalyst.Approximation F g p)
      (recv : Machine (64*w) tp tr tk) (raw gateBase : ℕ) (pins : Fin (E*2)→Bool)
      (sel : Fin (cap+1)→Bool),
      let W:=64*w
      let J:=GridDescription.sector w
      let K:=2^(3*w/5)
      let d:=(k+1)+w/2
      let G:=TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs words d
      let off:=1+(d+d)
      let rst:=E*2+w^2+bank*w^2
      let a:=TraceSeedWriter.archive B w (k+1) off G.cells cap rst
      let params:=GridStructuralHeader.parameters B (k+1) (s w) cap M fit hF st raw gateBase
      let field:=FieldCode.ofCardLe hF
      let capture:=GridSelfHeader.captured (B:=bank) X field params recv M pins (12*J) sel
      let input:=GridApproximationAdvice.paddedMemory X field bank (2*J) capture
      let source:=GridStructuralHeader.selectorBit cap sel
      let P:=B.repeat (s w)
      let rem:=k+1-P.charge
      let lanes : k+1=P.charge+rem := by dsimp only [P,rem];rw [B.charge_repeat];omega
      let native:=B.cursorState hk (w/2) off G.cells
      let A : State (2^B.exponent 0) (P.charge+rem):=lanes ▸ native
      let ss:=P.directory rem (k+1)
      let edges:=P.finalEdges rem (k+1)
      let origin:=TraceSeedWriter.memory a ss edges [] source input (s w)
      let r:=Physical.run B hk (w/2) off G.cells (s w) fits
      GridSelfHeader.rawSize w E bank (GridStructuralHeader.wordCount (GridStructuralHeader.directory (w:=w) B (k+1) (s w) cap).length
        (TraceReceiverTemplate.count G) (HistoryStageBody.Physical.libraryWords B (64*w)))≤J → 12*bank≤J → cap≤J → K≤cap →
      ∃ hword : B.repeatFactor*(native.maxWidth+1)*B.widthBase^(s w)<2^W,
        let table:=physicalTable B hk (w/2) off G.cells (s w) W fits hword
        let internal:=B.recordTable B.alphabetCap W (s w) rem A le_rfl
          (by rw [State.maxWidth_cast_lanes,←Nat.mul_assoc];exact hword)
        let proc:=program B a ss edges W (s w)
        Admission field proc.block proc.publicData (·=input)
          (fun _=>(GridSelector.read r.plan table.codes (fun h=>(r.terminalLayer h).state.widthSum)
            cap (List.ofFn (fun j : Fin cap=>sel j.succ))).isSome)
          (fun _ out=>Post a P rem A internal.records (2^w) K source input origin out)
          (K+(K+Archive.terminalTime (a.terminal ss edges W))) := by
  filter_upwards [TraceSeedWriter.eventual_initialize B scale (3*5*10^26*65^14) 15,
    eventual_native_port_count (F:=F) scale,native_machine_controller B scale,eventual_terminal_room B scale,
    eventual_record_length B scale,eventually_ge_atTop 2] with w seed ports loop terminal sizes hw
  intro pc regs words k S base fuel hk axes hp hr hs M fit hF st fits
    g p E bank tp tr tk cap X recv raw gateBase pins sel W J K d G off rst a params field
    capture input source P rem lanes native A ss edges origin r packed compact capacity cutoff
  let cur : Word W:=a.control
  let ctr : Word W:=((a.control+1 : ℕ) : Word W)
  have placed:=TraceSeedWriter.archive_placement B w (k+1) off G.cells cap rst
  have limits:=sector_placement_room (w:=w) (by omega)
  have bell : a.control+1<2^W := by
    rw [placed.control];change 16*2^(32*w)+6*(2^w)^4+1<2^(64*w)
    have pos := Nat.two_pow_pos w; have sq : 0<(2^w)^4 := by positivity
    exact lt_of_le_of_lt (by omega) limits.2
  have cursor : cur.val=a.control:=Fin.val_cast_of_lt (by omega)
  have cnt : ctr.val=a.control+1:=Fin.val_cast_of_lt bell
  have bounded : W*a.histWords ss≤K := by
    have count:=sizes (axes ▸ fits)
    have alphabet : a.K=B.alphabetCap := rfl
    simpa only [W,K,ss,P,rem,Archive.histWords,alphabet,stageCounts,←axes,Nat.mul_assoc,Nat.mul_comm,
      Nat.mul_left_comm] using count
  obtain ⟨dir,body,old⟩:=GridStructuralHeader.seeded_sources B (k+1) (s w) cap M fit hF st
    raw gateBase X field recv M pins sel off G.cells packed compact capacity
  have offset : rst≤13*J := by
    have : rst≤J := (Nat.le_add_right _ _).trans packed
    omega
  obtain ⟨first,visit,counter,roots,foot,frame⟩:=seed a k off G.cells hk fits axes rfl rfl rfl rfl
    (ports hp hr hs axes M fit hF st) rfl placed rfl rfl rfl capacity rst offset rfl rfl rfl rfl
    source input dir (fun i hi=>body i (hi.trans_le (bounded.trans cutoff)))
  have rawWin := old origin (fun z h=>frame z (.inl h))
  have bounds:=terminal (axes ▸ fits) a placed rfl rfl rfl rfl capacity
  rw [←axes] at bounds
  have two : 1<2^W := Nat.one_lt_two_pow (by dsimp only [W];omega)
  obtain ⟨word,checked⟩:=GridSelector.controller_terminal B hk fits (loop hp hr hs hk axes M fit hF st fits)
    a (16*J) cur ctr field placed cursor (by omega) rfl source origin cutoff bounded
    bounds.1 bounds.2 rawWin two
  refine ⟨word,?_⟩
  intro table internal proc
  have card : Fintype.card A.Base=k+1 := (Program.baseCast lanes native).trans (Fintype.card_fin _)
  intro pp rr kk machine pcMap regMap pubMap exit code rom cfg mem entry initial
  obtain ⟨yes,no⟩ := admission_seq field (TraceSeedWriter.procedure a ss edges (s w))
    ((NavigationPass.repeated cur ctr a.K B).seq (TerminalWireArchive.program (a.terminal ss edges W)))
    (good:=fun _=>(GridSelector.read r.plan table.codes (fun h=>(r.terminalLayer h).state.widthSum)
      cap (List.ofFn (fun j : Fin cap=>sel j.succ))).isSome)
    (admission_of_spec field _ first) checked (fun _ _ _=>trivial)
    (fun _ mid _ _ eq=>by
      subst mid
      refine ⟨⟨rfl,visit,counter⟩,?_⟩
      have capEq : a.pairCapacity = cap := rfl
      have bitsEq : List.ofFn (fun j : Fin cap => source j.val) =
          List.ofFn (fun j : Fin cap => sel j.succ) :=
        GridStructuralHeader.selector_body (cap:=cap) sel
      rw [capEq]
      change (GridSelector.read r.plan table.codes (fun h => (r.terminalLayer h).state.widthSum)
        cap (List.ofFn (fun j : Fin cap => source j.val))).isSome = true ↔ _
      rw [bitsEq])
    machine pcMap regMap pubMap exit code rom cfg mem entry initial
  refine ⟨fun live=>?_,no⟩
  obtain ⟨t,ht,last,out,returned,⟨mid,eq,saved⟩,steps⟩:=yes live
  subst mid
  refine ⟨t,ht,last,out,returned,?_,steps⟩
  refine ⟨?_,roots,foot,fun z hz=>frame z (.inl hz),?_⟩
  · simpa only [card] using visit.cast lanes
  simpa only [card] using saved


end
end Hierarchy.GridPhysicalAdmission

end OAI
