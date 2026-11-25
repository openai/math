import OAI.Hierarchy.GridSimulationPadding
import OAI.Hierarchy.TraceIterationTerminalRoom
import OAI.ThreeFlat.RAM.TickProcedureContracts

namespace OAI
/-! # The native histogram and terminal scans on a single full grid selector -/

namespace Hierarchy.GridSelector
open ThreeFlat RAM Diagonal Diagonal.HistoryContraction
open Diagonal.PhysicalStage Diagonal.NavigationPass Diagonal.NavigationDirectory Computability.VPVNP.BurstRAM
open RAM.PhysicalProcedure RAM.TickStageSpec
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F]

theorem take_window (source : ℕ→Bool) {cap cut : ℕ} (fits : cut≤cap) :
    (List.ofFn (fun i : Fin cap=>source i.val)).take cut =
      List.ofFn (fun i : Fin cut=>source i.val) := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left fits]
  · intro i h1 h2
    simp

/-- The native prefix ROM may leave different end states for different valid
histories. In each case its actual width and register receipts determine the
native terminal scan; rejected early branches keep zero mass. -/
theorem history_admission {W stages : ℕ} (a : Archive) (P : Program F stages) (rem : ℕ)
    (X : State (2^stages) (P.charge+rem)) (field : FieldCode F W)
    (E : (P.run rem X).Records) (source : ℕ→Bool) (origin : Memory W)
    (cur ctr : Word W) (limit cut prefixTime : ℕ) (loop : Procedure W)
    (pre : Memory W → Prop) :
    let r := P.run rem X
    let ss := P.directory rem (Fintype.card X.Base)
    let edges := P.finalEdges rem (Fintype.card X.Base)
    let x := a.terminal ss edges W
    let bits := r.readTerminal (fun A=>A.widthSum)
    let raw := List.ofFn (fun i : Fin a.pairCapacity=>source i.val)
    let short := List.ofFn (fun i : Fin cut=>source i.val)
    let H := W*a.histWords ss
    let seen := fun out=>
      a.TraceJournal limit cur ctr P rem X a.cursor short origin out ∧
      ∃ v : Run.WireLayer,r.EndsAt E short v (short.drop H) ∧ a.Visit ss edges source cur ss v.state out
    cut≤a.pairCapacity → H≤cut → (∀ h,(r.plan.write (r.codes E) h).length=H) →
    cur.val=a.control → cur.val<ctr.val → a.seed≤a.control → a.seed≤a.cursor.heap →
    a.cursor.header=a.seed+64 → a.seed+(a.directory ss edges W).length<2^W →
    a.TerminalRoom ss edges W → a.RawWindow ss source origin → 1<2^W →
    Admission field loop.block loop.publicData pre (fun _=>(r.plan.read (r.codes E) short).isSome)
      (fun _ out=>seen out) prefixTime →
    Admission field (loop.seq (TerminalWireArchive.program x)).block
      (loop.seq (TerminalWireArchive.program x)).publicData pre
      (fun _=>(read r.plan (r.codes E) bits a.pairCapacity raw).isSome)
      (fun _ final=>∃ mid,seen mid ∧ final=TerminalWireArchive.image x mid)
      (prefixTime+Archive.terminalTime x) := by
  intro r ss edges x bits raw short H seen cutFits histFits fixed atCtrl nextCtrl seedCtrl seedHeap
    head fits room window two admitted
  have trimmed : raw.take cut=short := take_window source cutFits
  have demand : (read r.plan (r.codes E) bits a.pairCapacity raw).isSome →
      (r.plan.read (r.codes E) short).isSome := by
    intro accepted
    rw [←trimmed]
    apply (short_read r.plan (r.codes E) raw cut (fun h=>(fixed h).le.trans histFits)).mpr
    cases parse : r.plan.read (r.codes E) raw with
    | none => simp [read,parse] at accepted
    | some pair => rfl
  have right : Admission field (TerminalWireArchive.program (W:=W) x).block
      (TerminalWireArchive.program x).publicData seen
      (fun _=>(read r.plan (r.codes E) bits a.pairCapacity raw).isSome)
      (fun mid out=>out=TerminalWireArchive.image x mid) (Archive.terminalTime x) := by
    intro p regs k M pc reg data stop rom pub cfg m start ok
    obtain ⟨j,v,ends,visit⟩ := ok
    have old (addr : ℕ) (below : addr<a.seed) : m addr=origin addr :=
      Archive.TraceJournal.frame P rem X a.cursor short j (by omega) (by omega)
        ⟨Or.inl (by omega),Or.inl (by omega)⟩
    have ptr : cur=(a.control:Word W) := by rw [←atCtrl]; simp
    have parsed : r.EndsAt E (raw.take cut) v ((raw.take cut).drop H) := by
      rw [trimmed]
      exact ends
    exact terminal_visit a P rem X field E source origin m v cut fixed
      parsed (ptr ▸ visit) head fits room window old two M pc reg data stop rom pub cfg m start rfl
  intro labels regs words machine
  exact admission_seq field loop (TerminalWireArchive.program x) admitted right
    (fun _ _ good=>demand good) (fun _ _ _ _ receipt=>⟨receipt,Iff.rfl⟩) machine

private theorem history_admission_at {W stages : ℕ} (a : Archive) (P : Program F stages) (rem : ℕ)
    (X : State (2^stages) (P.charge+rem)) (axes : ℕ) (axisCard : Fintype.card X.Base=axes)
    (field : FieldCode F W)
    (E : (P.run rem X).Records) (source : ℕ→Bool) (origin : Memory W)
    (cur ctr : Word W) (limit cut prefixTime : ℕ) (loop : Procedure W)
    (pre : Memory W → Prop) :
    let r := P.run rem X
    let ss := P.directory rem axes
    let edges := P.finalEdges rem axes
    let x := a.terminal ss edges W
    let bits := r.readTerminal (fun A=>A.widthSum)
    let raw := List.ofFn (fun i : Fin a.pairCapacity=>source i.val)
    let short := List.ofFn (fun i : Fin cut=>source i.val)
    let H := W*a.histWords ss
    let seen := fun out=>
      a.TraceJournal limit cur ctr P rem X a.cursor short origin out ∧
      ∃ v : Run.WireLayer,r.EndsAt E short v (short.drop H) ∧ a.Visit ss edges source cur ss v.state out
    cut≤a.pairCapacity → H≤cut → (∀ h,(r.plan.write (r.codes E) h).length=H) →
    cur.val=a.control → cur.val<ctr.val → a.seed≤a.control → a.seed≤a.cursor.heap →
    a.cursor.header=a.seed+64 → a.seed+(a.directory ss edges W).length<2^W →
    a.TerminalRoom ss edges W → a.RawWindow ss source origin → 1<2^W →
    Admission field loop.block loop.publicData pre (fun _=>(r.plan.read (r.codes E) short).isSome)
      (fun _ out=>seen out) prefixTime →
    Admission field (loop.seq (TerminalWireArchive.program x)).block
      (loop.seq (TerminalWireArchive.program x)).publicData pre
      (fun _=>(read r.plan (r.codes E) bits a.pairCapacity raw).isSome)
      (fun _ final=>∃ mid,seen mid ∧ final=TerminalWireArchive.image x mid)
      (prefixTime+Archive.terminalTime x) := by
  subst axes
  exact history_admission a P rem X field E source origin cur ctr limit cut prefixTime loop pre

private theorem read_cast {d l l' K W : ℕ} (e : l=l') (A : State d l)
    (r : Run F (e ▸ A : State d l')) {sizes : List ℕ} (q : Program.RecordTable r K W sizes)
    (cap : ℕ) (raw : List Bool) :
    (read (Program.recast e A r).plan (Program.changeTable e A r q).codes
      (fun h=>((Program.recast e A r).terminalLayer h).state.widthSum) cap raw).isSome =
    (read r.plan q.codes (r.readTerminal (fun X=>X.widthSum)) cap raw).isSome := by
  cases e
  change (read r.plan q.codes (fun h=>(r.terminalLayer h).state.widthSum) cap raw).isSome=_
  rw [show (fun h=>(r.terminalLayer h).state.widthSum)=r.readTerminal (fun X=>X.widthSum) from
    funext r.terminalLayer_width]

private theorem admission_reads {W : ℕ} (field : FieldCode F W) (first last : Procedure W)
    {pre : Memory W→Prop} {middle result : Memory W→Memory W→Prop} {t u : ℕ}
    {prefixResult physicalPrefix full physicalFull : Bool}
    (prefixEq : physicalPrefix=prefixResult) (fullEq : physicalFull=full)
    (scan : Admission field first.block first.publicData pre (fun _=>physicalPrefix) middle t)
    (finish : Admission field first.block first.publicData pre (fun _=>prefixResult) middle t →
      Admission field last.block last.publicData pre (fun _=>full) result u) :
    Admission field last.block last.publicData pre (fun _=>physicalFull) result u := by
  have scanned : Admission field first.block first.publicData pre (fun _=>prefixResult) middle t := by
    intro labels registers slots machine
    exact RAM.TickStageSpec.Admission.mono (fun {p r k} M=>scan M) (fun _ h=>h)
      (fun _ _=>(congrArg (fun b : Bool=>b=true) prefixEq).symm.to_iff) (fun _ _ _ _ h=>h) le_rfl machine
  intro labels registers slots machine
  exact RAM.TickStageSpec.Admission.mono (fun {p r k} M=>finish scanned M) (fun _ h=>h)
    (fun _ _=>(congrArg (fun b : Bool=>b=true) fullEq).to_iff) (fun _ _ _ _ h=>h) le_rfl machine

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- For the real self-programmable grid verifier, the public compressor and its
physical table select exactly the same full-tape simulations as the native
prefix program followed by its terminal-width and padding checker. -/
theorem controller_terminal (B : Block F) {w k n offs slots : ℕ} (hk : 2≤k+1)
    (fits : B.blockCharge*n≤k+1) (controller : TraceAdmission.ControllerAt B w k n offs slots hk fits)
    (arch : Archive) (base : ℕ) (cur ctr : Word (64*w)) (field : FieldCode F (64*w))
    (placed : TraceAdmission.ArchivePlacement arch base w) (ptr : cur.val=arch.control)
    (counter : cur.val<ctr.val) (alphabet : arch.K=B.alphabetCap)
    (source : ℕ→Bool) (origin : Memory (64*w)) :
    let W := 64*w
    let cut := 2^(3*w/5)
    let P:=B.repeat n
    let rem:=k+1-P.charge
    let e : k+1=P.charge+rem := by dsimp only [P,rem];rw [B.charge_repeat];omega
    let X:=B.cursorState hk (w/2) offs slots
    let A : State (2^B.exponent 0) (P.charge+rem):=e ▸ X
    let ss:=P.directory rem (k+1)
    let edges:=P.finalEdges rem (k+1)
    let x:=arch.terminal ss edges W
    let short:=List.ofFn (fun j : Fin cut=>source j.val)
    let raw:=List.ofFn (fun j : Fin arch.pairCapacity=>source j.val)
    let r:=TraceDistribution.Physical.run B hk (w/2) offs slots n fits
    let loop:=NavigationPass.repeated cur ctr arch.K B
    cut≤arch.pairCapacity → W*arch.histWords ss≤cut →
    arch.seed+(arch.directory ss edges W).length<2^W → arch.TerminalRoom ss edges W →
    arch.RawWindow ss source origin → 1<2^W →
    ∃ hword : B.repeatFactor*(X.maxWidth+1)*B.widthBase^n<2^W,
      let table:=TraceAdmission.physicalTable B hk (w/2) offs slots n W fits hword
      let internal:=B.recordTable B.alphabetCap W n rem A le_rfl
        (by rw [State.maxWidth_cast_lanes,←Nat.mul_assoc];exact hword)
      Admission field (loop.seq (TerminalWireArchive.program x)).block
        (loop.seq (TerminalWireArchive.program x)).publicData
        (fun m=>m=origin ∧ arch.Visit ss edges source cur [] X m ∧ (m ctr.val).val=n)
        (fun _=>(read r.plan table.codes (fun h=>(r.terminalLayer h).state.widthSum)
          arch.pairCapacity raw).isSome)
        (fun _ final=>∃ mid,(arch.TraceJournal (2^w) cur ctr P rem A arch.cursor short origin mid ∧
          ∃ v : Run.WireLayer,(P.run rem A).EndsAt internal.records short v (short.drop (W*arch.histWords ss))
            ∧ arch.Visit ss edges source cur ss v.state mid) ∧ final=TerminalWireArchive.image x mid)
        (cut+Archive.terminalTime x) := by
  intro W cut P rem e X A ss edges x short raw r loop cutFits recordFits header room window two
  obtain ⟨word,scan⟩ := controller arch base edges cur ctr field placed ptr counter alphabet source origin
  refine ⟨word,?_⟩
  intro table internal
  have axes : Fintype.card A.Base=k+1 := (Program.baseCast e X).trans (Fintype.card_fin _)
  have eqRead : (r.plan.read table.codes short).isSome =
      ((P.run rem A).plan.read internal.codes short).isSome :=
    TraceAdmission.valid_cast e X (P.run rem A) internal short
  have eqFull : (read r.plan table.codes (fun h=>(r.terminalLayer h).state.widthSum)
      arch.pairCapacity raw).isSome =
      (read (P.run rem A).plan internal.codes ((P.run rem A).readTerminal (fun S=>S.widthSum))
        arch.pairCapacity raw).isSome := read_cast e X (P.run rem A) internal _ _
  have fixed (h : (P.run rem A).plan.History) :
      ((P.run rem A).plan.write internal.codes h).length=W*arch.histWords ss := by
    rw [internal.write_size]
    simp only [ss,P,Archive.histWords,alphabet,axes,Nat.mul_comm]
  have seedHeap : arch.seed≤arch.cursor.heap := by rw [placed.seed,placed.heap];omega
  have seedCtrl : arch.seed≤arch.control := by rw [placed.seed,placed.control];omega
  have head : arch.cursor.header=arch.seed+64 := by rw [placed.header,placed.seed]
  let pre := fun m=>m=origin ∧ arch.Visit ss edges source cur [] X m ∧ (m ctr.val).val=n
  let seen := fun (_ : Memory W) mid=>
    arch.TraceJournal (2^w) cur ctr P rem A arch.cursor short origin mid ∧
    ∃ v : Run.WireLayer,(P.run rem A).EndsAt internal.records short v (short.drop (W*arch.histWords ss)) ∧
      arch.Visit ss edges source cur ss v.state mid
  intro labels registers machineSlots machine
  exact admission_reads field loop (loop.seq (TerminalWireArchive.program x))
    (pre:=pre) (middle:=seen) (t:=cut) (u:=cut+Archive.terminalTime x)
    eqRead eqFull (fun {p r k} M=>scan M)
    (fun acceptedPrefix {pc regs slots} M=>history_admission_at arch P rem A (k+1) axes field internal.records source origin
      cur ctr (2^w) cut cut loop pre cutFits recordFits fixed ptr counter seedCtrl seedHeap head header room
      window two acceptedPrefix M) machine


end
end Hierarchy.GridSelector

end OAI
