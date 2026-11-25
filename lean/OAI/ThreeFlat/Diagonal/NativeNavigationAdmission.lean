import OAI.ThreeFlat.Diagonal.PhysicalNodeChargeFits
import OAI.ThreeFlat.Diagonal.TickTotalBudget
import OAI.ThreeFlat.Diagonal.NavigationCursorPairSpace
import OAI.ThreeFlat.Diagonal.AlignedHShape
import OAI.ThreeFlat.Diagonal.InitialSeedVisit
import OAI.ThreeFlat.Diagonal.PhysicalNodeArchiveStored
import OAI.ThreeFlat.Diagonal.PhysicalNodeClosedMounts
import OAI.ThreeFlat.Diagonal.NavigationRootPublication

namespace OAI
/-! # Successive native passes of the chronological tick navigator -/

set_option quotPrecheck false

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open PhysicalStage NavigationDirectory NodePublication TickPhaseModel TickChronology TickAuxiliary
open RAM.TickActiveROM RAM.TickPhysicalABI RAM.TickBitRelation RAM.TickIntervalCursor
open RAM.HistoryFactors RAM.Contraction RAM.BitLayout
open scoped Classical Fin.CommRing

variable {W : ℕ} {F : Type} [Field F] [Fintype F]

/-- Range and layout facts for the actual root scan and the selected tick. -/
structure RootLimits {S : HistoryContraction.Shape} {P : HistoryContraction.Plan F S} {bits : P.History→ℕ} {c : Clock}
    {A : TickActiveROM.Layout} {span p H J : ℕ} {fit : Fits (TickWeightedBank.shape F p H J) W}
    (a : RootArchive) (T : Buckets P bits c A.bits a.initialLanes span) (v : HistoryContraction.Plan.Terminal P bits)
    (t : ℕ) (cell : TickActiveROM.CellInput A c fit) : Prop where
  sCount : A.intervalCount=TickWorkspace.base a.age 6
  sTable : A.intervalTable=TickWorkspace.base a.age 5
  sMap : A.intervalMap=TickWorkspace.base a.age 7
  sCounters : A.groupCounts=TickWorkspace.base a.age 8
  chunkBits : a.chunkBits=A.bits
  total : a.totalPairs=c.chunks*A.bits
  width : a.pairsPerLane=span
  ng : a.groups=c.groups
  groupFits : a.groups<2^W
  space : TickWorkspace.base a.age 5+4*a.initialLanes≤TickWorkspace.base a.age 6
  bounds : WordBounds A fit
  ranges : ScanRanges A (T.finiteRows v).length W
  chunkFit : cell.lo+A.bits<2^W
  grpFit : c.group t<2^W
  clkFit : A.clockWords<2^W
  clo : A.clockWords+3<a.protectedBelow
  ctl : A.control+3<a.protectedBelow
  oaFit : A.oldAux+A.bits≤a.protectedBelow
  naFit : A.newAux+A.bits≤a.protectedBelow
  ocFit : A.oldChunk+A.bits≤a.protectedBelow
  ncFit : A.newChunk+A.bits≤a.protectedBelow

/-- Word images mounted at the root pass and the two clock and four boundary ranges. -/
structure RootMemory {c : Clock}
    {A : TickActiveROM.Layout} (a : RootArchive) (t : ℕ) (oa na oc nc : Aux A.bits)
    (ls : List Layers) (m : Memory W) (team : ℕ) : Prop where
  headers : Mount a.headerImage a.headerData m
  stages : Mount a.stageImage (a.stageData ls) m
  clock : TickPhysicalABI.Inputs A c m team t
  mountedOld : ∀ i : Fin A.bits,m (A.oldAux+i.val)=TickBitRelation.bitWord W (oa i)
  mountedNew : ∀ i : Fin A.bits,m (A.newAux+i.val)=TickBitRelation.bitWord W (na i)
  chunkOld : ∀ i : Fin A.bits,m (A.oldChunk+i.val)=TickBitRelation.bitWord W (oc i)
  chunkNew : ∀ i : Fin A.bits,m (A.newChunk+i.val)=TickBitRelation.bitWord W (nc i)


/-- All operands of the accepted physical root publication. -/
structure RootInputs {S : HistoryContraction.Shape} {P : HistoryContraction.Plan F S} {bits : P.History→ℕ} {c : Clock}
    {A : TickActiveROM.Layout} {span p H J : ℕ} {fit : Fits (TickWeightedBank.shape F p H J) W}
    (a : RootArchive) (T : Buckets P bits c A.bits a.initialLanes span) (v : HistoryContraction.Plan.Terminal P bits)
    (t : ℕ) (oa na oc nc : Aux A.bits) (cell : TickActiveROM.CellInput A c fit)
    (nodes : RootArchive.Nodes a) (teams : ℕ) (ls : List Layers) (m : Memory W) (team : ℕ)
    : Prop extends RootLimits a T v t cell, RootMemory (c:=c) (A:=A) a t oa na oc nc ls m team where
  geometry : RootArchive.PublishRoom a W
  schedule : RootArchive.ScheduleFacts a W teams nodes.work nodes.pairs a.ids
  home : ∀ i,finCongr ng (a.groupOf nodes teams schedule groupFits (nodes.laneRoot geometry.lanes i))=
    T.group v.1 (P.destination v.1 (T.site i))

section RootPass

variable {S : HistoryContraction.Shape} {P : HistoryContraction.Plan F S} {bits : P.History→ℕ} {c : Clock} {A : TickActiveROM.Layout}
  {span p H J : ℕ} {fit : Fits (TickWeightedBank.shape F p H J) W}
  (a : RootArchive) (T : Buckets P bits c A.bits a.initialLanes span) (v : HistoryContraction.Plan.Terminal P bits)
  (t : ℕ) (oa na oc nc : Aux A.bits) (pairFit : 1+A.capacity+2*T.length v (c.group t)≤A.bits)
  (N : BitNetwork F p) (L : Library N) (hh : N.internal≤H) (hj : N.cells+(H-N.internal)≤J)
  (lut : A.lut+8*(L.count+2)≤2^W)
local notation "cell" => T.cellInput (fit:=fit) v t oa pairFit N L hh hj lut

theorem RootInputs.execute {nodes : RootArchive.Nodes a} {teams : ℕ} {ls : List Layers}
    {m : Memory W} {team : ℕ} (i : RootInputs a T v t oa na oc nc cell nodes teams ls m team)
    (stored : nodes.Stored m) :
    (a.publish (W:=W)).Spec (·=m) (fun _ out => NavOutput cell (c.phase t) oa na oc nc
      (a.preparedInput cell nodes teams ls m (a.groupOf nodes teams i.schedule i.groupFits ∘ nodes.laneRoot i.geometry.lanes)) out) (a.publishCost W) := by
  exact RootArchive.publish_nav a T v t oa pairFit N L hh hj lut nodes teams ls m
    i.geometry i.schedule i.headers i.stages stored i.sCount i.sTable i.sMap i.sCounters i.chunkBits
    i.total i.width i.ng i.groupFits i.home i.space i.bounds i.ranges i.chunkFit i.grpFit i.clkFit
    i.clo i.ctl i.oaFit i.naFit i.ocFit i.ncFit na oc nc team i.clock i.mountedOld i.mountedNew
    i.chunkOld i.chunkNew


end RootPass

private theorem spec_of_each {P : Procedure W} {pre : Memory W→Prop}
    {post : Memory W→Memory W→Prop} {time : ℕ}
    (each : ∀ m,pre m→P.Spec (·=m) (fun _ o=>post m o) time) : P.Spec pre post time := by
  intro n r k M pc reg pub exit inst values cfg m start input
  exact each m input M pc reg pub exit inst values cfg m start rfl

/-- All word-address and cost recurrences consumed by the native root publisher are
determined at the output of this same two-scan physical stage. -/
structure ArchiveInputs {d l : ℕ} {X : State d l} (r : Run F X) (h : r.plan.History)
    (C : r.Charges) (O : X.ArchiveSites) (path : r.ArchivePath h C O) (seed : LayerData O.layer)
    (n : NodeArchive) (m : Memory W) (budget : ℕ) (start pay : X.Site→ℕ) : Prop where
  room : RunBounds W n (records (r.archiveList h C O path seed)) budget
  tape : TapeBounds W n (records (r.archiveList h C O path seed))
  raw : let rows:=records (r.archiveList h C O path seed)
    Mount (image n rows.length) (tapeWord n rows) m
  source : SourceRows n (program (r.archiveList h C O path seed)) m
  initial : State.SeedRows O seed n.banks start pay
  fits : r.ArchiveFits W n.banks.unitWork h C start pay

def nodeTime (W n budget : ℕ) := (16*n*(5*W+6)+10)+(3+(3+(n*(7+budget)+4)))


end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.TickPhysicalABI
open PhysicalStage NavigationDirectory NodePublication TickPhaseModel TickChronology TickAuxiliary
open RAM.TickActiveROM RAM.TickBitRelation RAM.TickIntervalCursor RAM.HistoryFactors RAM.Contraction RAM.BitLayout
open scoped Classical Fin.CommRing

variable {W : ℕ} {F : Type} [Field F] [Fintype F] {d l : ℕ} {X : State d l}
variable {S : HistoryContraction.Shape} {P : HistoryContraction.Plan F S} {bits : P.History→ℕ} {c : Clock} {A : TickActiveROM.Layout}
  {span p H J : ℕ} {fit : Fits (TickWeightedBank.shape F p H J) W}

/-- The history and site order extracted from the successful stage projection. The
physical cursor layout fixes the exact directory and the terminal root interval. -/
structure Selection (r : Run F X) (C : r.Charges) (O : X.ArchiveSites) (seed : LayerData O.layer)
    (start pay : X.Site→ℕ) (n : NodeArchive) (a : RootArchive) (rows : List Layers)
    (budget : ℕ) (m : Memory W) where
  history : r.plan.History
  path : r.ArchivePath history C O
  source : ArchiveInputs r history C O path seed n m budget start pay
  layout : records (r.archiveList history C O path seed)=rows
  zero : O.layer.first=0
  first : a.firstFinal=(r.finalArchive history C O path).1.first
  card : a.rootCount=(r.finalArchive history C O path).1.count
  numbered : r.FinalNumbered history C O path
  stageK : ℕ
  headerEnd : ℕ
  heapEnd : ℕ
  visits : r.ArchiveVisits (RecordedStep stageK (n.banks.current:Word W) (n.counter:Word W)
    headerEnd heapEnd m) history C O path


variable (r : Run F X) (C : r.Charges) (O : X.ArchiveSites) (seed : LayerData O.layer)
  (start pay : X.Site→ℕ) (n : NodeArchive) (a : RootArchive) (rows : List Layers) (budget : ℕ)
  (T : Buckets P bits c A.bits a.initialLanes span) (v : HistoryContraction.Plan.Terminal P bits)
  (t : ℕ) (oa na oc nc : Aux A.bits) (pairFit : 1+A.capacity+2*T.length v (c.group t)≤A.bits)
  (N : BitNetwork F p) (L : Library N) (hh : N.internal≤H) (hj : N.cells+(H-N.internal)≤J)
  (lut : A.lut+8*(L.count+2)≤2^W)
local notation "cell" => T.cellInput (fit:=fit) v t oa pairFit N L hh hj lut

section
variable {r C O seed start pay n a rows budget}

def Selection.AtDirectory {m : Memory W} (s : Selection r C O seed start pay n a rows budget m)
    (K : ℕ) (stop : Cursor) : Prop :=
  s.stageK=K ∧ s.headerEnd=stop.header ∧ s.heapEnd=stop.heap

def Selection.AtProgram {m : Memory W} (s : Selection r C O seed start pay n a rows budget m)
    (K : ℕ) (stop : Cursor) (J : ∀ Pins : Type, Run.Assembler r Pins) (allow : StaticMotif F→Prop) : Prop :=
  s.AtDirectory K stop ∧ ∀ (Pins : Type) (L : X.Words Pins),
    r.WordVisits (RecordedWordStep K (n.banks.current : Word W) (n.counter : Word W)
      stop.header stop.heap m Pins allow) s.history (J Pins).steps L C O s.path


omit [Fintype F] in
theorem Selection.AtProgram.ordered {m : Memory W} {s : Selection r C O seed start pay n a rows budget m}
    {K : ℕ} {stop : Cursor} {J : ∀ Pins : Type, Run.Assembler r Pins} {allow : StaticMotif F→Prop}
    (profile : s.AtProgram K stop J allow) (Pins : Type) (L : X.Words Pins) :
    r.OrderedArchive s.history (J Pins).steps L C O s.path := by
  refine r.wordVisits_mono _ Run.childVisit ?_ s.history (J Pins).steps L C O s.path (profile.2 Pins L)
  intro d l D H A R i layout word sites charge row seen
  exact seen.elim (fun shrink=>shrink.childOrder) (fun refresh=>refresh.childOrder)

/-- Numbered old and new half records at one physical occurrence, in the same retained RAM. -/
def consecutiveHalfRows (Pins : Type) (safe : ℕ→Prop) (m : Memory W) : Run.WordVisit F Pins :=
  fun _ _ _ _ old _ row=>State.HalfRows old safe (fun x=>(m x).val) ∧
    State.HalfRows row.sites safe (fun x=>(m x).val)

omit [Fintype F] in
private theorem halfRows_along {Pins : Type} {K hi heap : ℕ} {cur ctr : Word W}
    {m : Memory W} {allow : StaticMotif F→Prop} {safe : ℕ→Prop} {tariff : ℕ}
    (positive : 0<tariff) (included : ∀ z,hi≤z ∧ z<heap→safe z)
    {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O)
    (start pay : A.Site→ℕ) (floor : r.LocalFloor C) (fits : r.ArchiveFits W tariff h C start pay)
    (facts : r.WordVisits (RecordedWordStep K cur ctr hi heap m Pins allow) h J L C O p)
    (here : State.HalfRows O safe (fun x=>(m x).val)) :
    r.WordVisits (consecutiveHalfRows Pins safe m) h J L C O p := by
  induction r with
  | done A=>trivial
  | step R next ih=>
    let j:=h.1
    let C' := C.1 j
    have small (v : (R.next j).Site) : (R.next j).incidentWidth v<2^W := by
      have cap:=((next j).fits_here fits.2 v).1
      have baseCost := (floor j).1 v
      have add : C' v≤R.push j C' start v:=Nat.le_add_right ..
      have times : R.push j C' start v≤tariff*R.push j C' start v:=Nat.le_mul_of_pos_left _ positive
      exact (show (R.next j).incidentWidth v≤C' v by dsimp only [C'];omega).trans_lt
        ((add.trans times).trans_lt cap)
    have fresh : State.HalfRows p.1.sites (fun x=>hi≤x ∧ x<heap) (fun x=>(m x).val) :=
      facts.1.elim (fun shrink=>shrink.halfRows) (fun refresh=>refresh.halfRows small)
    have kept := fresh.transfer (fun _ _=>rfl) included
    refine ⟨⟨here,kept⟩,?_⟩
    exact ih j (Run.tailHistory R next h) (J.2 j) (J.1 L j).words (C.2 j) p.1.sites p.2
      (R.push j C' start) _ (floor j).2 fits.2 facts.2 kept

omit [Fintype F] in
theorem Selection.AtProgram.halfRows {m : Memory W} {s : Selection r C O seed start pay n a rows budget m}
    {K : ℕ} {stop : Cursor} {J : ∀ Pins : Type, Run.Assembler r Pins} {allow : StaticMotif F→Prop}
    (profile : s.AtProgram K stop J allow) (Pins : Type) (L : X.Words Pins) (safe : ℕ→Prop)
    (seedRows : State.HalfRows O safe (fun x=>(m x).val))
    (included : ∀ z,stop.header≤z ∧ z<stop.heap→safe z) (unit : 0<n.banks.unitWork)
    (floor : r.LocalFloor C) :
    r.WordVisits (consecutiveHalfRows Pins safe m) s.history (J Pins).steps L C O s.path :=
  halfRows_along unit included r s.history (J Pins).steps L C O s.path start pay floor s.source.fits
    (profile.2 Pins L) seedRows


end

/-- The final scan's source words are required only at the unique actual output memory
of the selected node writer. The scheduler and its slot input use those very nodes. -/
def Selection.RootWords {m : Memory W} (s : Selection r C O seed start pay n a rows budget m)
    (teams team : ℕ) (slot : Memory W→Prop) : Prop :=
  ∀ out : Memory W, out=state n (program (r.archiveList s.history C O s.path seed)) m rows.length →
  O.Charged a.nodeBank (natural out) start pay →
  ∀ rs : r.ArchiveRowsStored a.nodeBank (natural out) s.history C O s.path,
    let ns:=RootArchive.nodesOfRun a r s.history C O s.path out rs s.zero s.first s.card start pay
    ∃ i : RootInputs a T v t oa na oc nc cell ns teams rows out team,
      ∀ u, a.preparedInput cell ns teams rows out
        (a.groupOf ns teams i.schedule i.groupFits ∘ ns.laneRoot i.geometry.lanes) u → slot u

/-- The selector of a history tree receives the same successful journal and retained
root directory as the native publisher. All three memory snapshots are actual machine
states at that branch, and the decoded history is constrained by the caller. -/
def CursorSlot (closed : Memory W→Prop) (selected : r.plan.History→Prop) (teams team : ℕ)
    (certify : ∀ m : Memory W, Selection r C O seed start pay n a rows budget m → Prop := fun _ _ => True)
    (slotMem : Memory W) : Prop :=
  ∃ mid : Memory W, closed mid ∧
    ∃ s : Selection r C O seed start pay n a rows budget mid, selected s.history ∧ certify mid s ∧
    ∃ out : Memory W, out=state n (program (r.archiveList s.history C O s.path seed)) mid rows.length ∧
      O.Charged a.nodeBank (natural out) start pay ∧
      ∃ rs : r.ArchiveRowsStored a.nodeBank (natural out) s.history C O s.path,
        let ns:=RootArchive.nodesOfRun a r s.history C O s.path out rs s.zero s.first s.card start pay
        ∃ i : RootInputs a T v t oa na oc nc cell ns teams rows out team,
          a.preparedInput cell ns teams rows out
            (a.groupOf ns teams i.schedule i.groupFits ∘ ns.laneRoot i.geometry.lanes) slotMem

theorem Selection.rootWords_of_inputs {m : Memory W} (s : Selection r C O seed start pay n a rows budget m)
    (closed : Memory W→Prop) (select : r.plan.History→Prop) (accepted : closed m) (h : select s.history)
    (teams team : ℕ)
    (reads : ∀ out : Memory W, out=state n (program (r.archiveList s.history C O s.path seed)) m rows.length →
      O.Charged a.nodeBank (natural out) start pay →
      ∀ rs : r.ArchiveRowsStored a.nodeBank (natural out) s.history C O s.path,
        let ns:=RootArchive.nodesOfRun a r s.history C O s.path out rs s.zero s.first s.card start pay
        RootInputs a T v t oa na oc nc cell ns teams rows out team)
    (certify : ∀ m,Selection r C O seed start pay n a rows budget m→Prop) (certified : certify m s) :
    Selection.RootWords (fit:=fit) r C O seed start pay n a rows budget T v t oa na oc nc
      pairFit N L hh hj lut s teams team (CursorSlot (fit:=fit) r C O seed start pay n a rows budget
        T v t oa na oc nc pairFit N L hh hj lut closed select teams team certify) := by
  intro out stateEq charged stored
  let i:=reads out stateEq charged stored
  exact ⟨i,fun mem prepared=>⟨m,accepted,s,h,certified,out,stateEq,charged,stored,i,prepared⟩⟩

set_option maxHeartbeats 1600000 in
theorem archive_root_spec (m : Memory W) (s : Selection r C O seed start pay n a rows budget m)
    (sameBank : n.banks=a.nodeBank) (teams team : ℕ) (slot : Memory W→Prop)
    (inputs : Selection.RootWords (fit:=fit) r C O seed start pay n a rows budget T v t oa na oc nc
      pairFit N L hh hj lut s teams team slot) :
    ((n.publish rows.length).seq (a.publish (W:=W))).Spec (·=m)
      (fun _ mem=>NavOutput cell (c.phase t) oa na oc nc slot mem)
      (nodeTime W rows.length budget+a.publishCost W) := by
  let xs:=r.archiveList s.history C O s.path seed
  let mid : Memory W→Prop := fun out=>
    out=state n (program xs) m rows.length ∧ O.Charged n.banks (natural out) start pay ∧
      r.ArchiveRowsStored n.banks (natural out) s.history C O s.path
  have write : (n.publish rows.length).Spec (·=m) (fun _ out=>mid out) (nodeTime W rows.length budget) := by
    let publishes (count : ℕ) : Prop := (n.publish count).Spec (·=m)
      (fun _ out => out=state n (program xs) m count ∧ O.Charged n.banks (natural out) start pay ∧
        r.ArchiveRowsStored n.banks (natural out) s.history C O s.path) (nodeTime W count budget)
    have native : publishes (records xs).length := by
      intro programs registers slots M
      exact publish_stored r s.history C O s.path seed n m s.source.room s.source.tape s.source.raw
        s.source.source start pay s.source.initial s.source.fits M
    have lengthEq : (records xs).length = rows.length := congrArg List.length s.layout
    change publishes rows.length
    rw [←lengthEq]
    exact @native
  have root : (a.publish (W:=W)).Spec mid (fun _ out=>NavOutput cell (c.phase t) oa na oc nc slot out)
      (a.publishCost W) := by
    apply spec_of_each
    rintro out ⟨eq,charged,rs⟩
    rw [sameBank] at charged rs
    let ns:=RootArchive.nodesOfRun a r s.history C O s.path out rs s.zero s.first s.card start pay
    have stored : ns.Stored out := RootArchive.nodesOfRun_stored a r s.history C O s.path out rs s.zero
      s.first s.card start pay charged
    obtain ⟨i,keep⟩:=inputs out eq charged rs
    intro programs registers slots M
    refine Procedure.Spec.mono (RootInputs.execute a T v t oa na oc nc pairFit N L hh hj lut i stored)
      (fun _ h=>h) ?_ le_rfl M
    intro init final h
    exact {h with evalInputs:=fun hp=>keep _ (h.evalInputs hp)}
  intro programs registers slots M
  exact Procedure.Spec.mono (Procedure.Spec.seq write root (fun _ _ equal=>equal)) (fun _ h=>h)
    (fun _ _ witness=>witness.choose_spec.2) le_rfl M

/-- Admitted and rejected paths both execute the fixed native three-pass program.
A rejecting traversal delivers zero before the two publication passes can execute. -/
theorem navigation_admission (field : FieldCode F W) (B : Block F) (archive : Archive)
    (blocks rem finalEdges : ℕ) (directory : rows=nodeLayers archive.K
      ((B.repeat blocks).directory rem archive.axes) archive.cursor archive.seedLayer)
    (same : n.banks=a.nodeBank) (input : Memory W) (good : Prop)
    (closed : Memory W→Prop) (activeTime teams team : ℕ) (slot : Memory W→Prop)
    (active : let front:=NavigationPass.active (W:=W) archive B blocks rem finalEdges
      TickStageSpec.Admission field front.block front.publicData (·=input) (fun _=>good)
        (fun _ out=>closed out) activeTime)
    (selected : ∀ m, closed m → ∃ s : Selection r C O seed start pay n a rows budget m,
      Selection.RootWords (fit:=fit) r C O seed start pay n a rows budget T v t oa na oc nc
        pairFit N L hh hj lut s teams team slot) :
    let machine := navigation (W:=W) archive n a B blocks rem finalEdges
    TickStageSpec.Admission field machine.block machine.publicData (·=input) (fun _=>good)
      (fun _ mem=>NavOutput cell (c.phase t) oa na oc nc slot mem)
      (activeTime+(nodeTime W rows.length budget+a.publishCost W)) := by
  have tail : ((n.publish rows.length).seq (a.publish (W:=W))).Spec closed
      (fun _ final=>NavOutput cell (c.phase t) oa na oc nc slot final)
      (nodeTime W rows.length budget+a.publishCost W) := by
    apply spec_of_each
    intro m done
    obtain ⟨s,i⟩:=selected m done
    intro programs registers slots M
    exact archive_root_spec r C O seed start pay n a rows budget T v t oa na oc nc
      pairFit N L hh hj lut m s same teams team slot i M
  let passes (count : ℕ) := (NavigationPass.active (W:=W) archive B blocks rem finalEdges).seq
    ((n.publish count).seq (a.publish (W:=W)))
  have programEq : navigation (W:=W) archive n a B blocks rem finalEdges = passes rows.length :=
    congrArg passes (congrArg List.length directory.symm)
  rw [programEq]
  intro machine programs registers slots M
  exact TickStageSpec.Admission.mono
    (TickStageSpec.admission_seq field (NavigationPass.active archive B blocks rem finalEdges)
      ((n.publish rows.length).seq (a.publish (W:=W))) (good:=fun _=>good)
      active (TickStageSpec.admission_of_spec field _ tail) (fun _ _ accepted=>accepted)
      (fun _ _ _ ok out=>⟨out,Iff.intro (fun _=>ok) (fun _=>trivial)⟩))
    (fun _ h=>h) (fun _ _=>Iff.rfl) (fun _ _ _ _ hs=>hs.choose_spec.2) le_rfl M


end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive

open Computability.VPVNP.BurstRAM RAM PhysicalStage NavigationDirectory
variable {F : Type} [Field F] [Fintype F]

/-- The actual two-half aligned matrix needs at most one chunk of group counters.
The estimate keeps the true period, offset and tick count of the selected H shape. -/
theorem aligned_groups {u b A ℓ : ℕ} (params arg tpl : ℕ) (hu : 40≤u) (clock : ℓ≤u^6) :
    let shape := AlignedHShape.shape u b A ℓ params arg tpl
    1024*(2*shape.chunks)≤2^(u^10-u^4) := by
  intro shape
  have pos : 0<u := by omega
  have u3 : u^3≤u^6 := Nat.pow_le_pow_right pos (by decide)
  have u4 : u^4≤u^6 := Nat.pow_le_pow_right pos (by decide)
  have v : u≤u^6 := Nat.le_self_pow (by decide) _
  have gap : 40*u^6≤u^10 := by
    have big : 40≤u^4 := hu.trans (Nat.le_self_pow (by decide) _)
    exact (Nat.mul_le_mul_right (u^6) big).trans_eq (by ring)
  have ticks : shape.inside+1=2^ℓ := AlignedHShape.ticks params arg tpl
  change 1024*(2*(2^(u^3+u^4-b*(A+2))*(shape.inside+1)))≤_
  rw [ticks,show (1024:ℕ)=2^10 by decide,show (2:ℕ)*(2^(u^3+u^4-b*(A+2))*2^ℓ)=
    2^(1+((u^3+u^4-b*(A+2))+ℓ)) by rw [pow_add,pow_one,pow_add],←pow_add]
  apply Nat.pow_le_pow_right (by decide)
  omega

/-- The chosen physical root archive has room in the scratch banks, and the full native
execution stays below a fixed polynomial times one chunk, including the clipped scan over
every lane and the complete final group and chunk ranges. -/
theorem cursor_root_sizes_budget (B : Block F) {u rem low stride cells off tariff : ℕ}
    (shape : PhysicalPinsExpr.Shape) (hu : 40≤u) (levels : B.levels+1≤u)
    (factor : B.allocations.sum≤u) (half : low=u^10/2)
    (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6)
    (groups : 1024*(2*shape.chunks)≤2^(u^10-u^4))
    (bits : shape.bits≤2^(u^10-u^4)) (pairs : 2*shape.halfBits≤2^(3*u^10)) :
    let W := 16*u^10
    let p := Parameters.cursor B u rem low stride cells shape off tariff
    let A := p.archive (2^B.exponent 0) W
    let ss := (B.repeat (u^8)).directory rem p.axes
    let N := p.nodeArchive A ss W
    let R := p.rootArchive A N ss W
    let chunk := 2^(u^10-u^4)
    (R.initialLanes≤R.rootsTotal → R.stageRaw+W*(4*R.stageCount)≤R.header → R.PublishSizes W) ∧
      R.publishCost W≤100000*u^20*chunk := by
  intro W p A ss N R chunk
  let k := (B.repeat (u^8)).charge+rem
  let v := u^10
  have pos : 0<u := by omega
  have vpos : 0<v := Nat.pow_pos pos
  have ch : 0<chunk := Nat.two_pow_pos _
  have stages : ss.length≤u^9 := by
    change ((B.repeat (u^8)).directory rem p.axes).length≤u^9
    rw [Program.directory_length,program_length,B.repeat_effects_length]
    exact (Nat.mul_le_mul_right _ levels).trans_eq (by ring)
  have high : u^9≤v := Nat.pow_le_pow_right pos (by decide)
  have stageCount : R.stageCount=ss.length+1 := rfl
  have byte : 8*R.rootsTotal≤chunk :=
    (node_count_space B p hu levels factor half depth (by rfl)).2.1
  have lane : R.initialLanes≤chunk := by
    have h := (register_exponents (k:=k) (e:=0) (by omega : 16≤u) (by omega) half depth).1
    have cap : 8*2^k ≤ chunk := by simpa only [pow_zero,one_mul] using h
    exact (Nat.le_mul_of_pos_left (2^k) (by decide : 0<8)).trans cap
  have size : chunk≤TickWorkspace.stride u :=
    (Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le (u^10) (u^4))).trans
      (Nat.le_self_pow (by decide : 4≠0) _)
  have big : 128≤TickWorkspace.stride u := by
    have us : u≤u^10 := Nat.le_self_pow (by decide) _
    have radix : 2^7≤(2:ℕ)^(u^10) := Nat.pow_le_pow_right (by decide) (by omega)
    exact radix.trans (Nat.le_self_pow (by decide : 4≠0) _)
  constructor
  · intro enough raw
    refine ⟨big,?_,byte.trans size,enough,B.directory_header_space hu levels rem p.axes,
      groups.trans size,bits.trans size,?_,?_,raw⟩
    · exact (Nat.le_add_right _ _).trans_lt (TickWorkspace.word_space (u:=u) (i:=50) (by omega) (by omega))
    · change 2^k*2^low<2^W
      rw [←pow_add]
      apply Nat.pow_lt_pow_right (by decide)
      have small : u^6≤v := Nat.pow_le_pow_right pos (by decide)
      change k+low<16*v
      change k+low≤v+2*u^6 at depth
      omega
    · exact pairs.trans_lt (Nat.pow_lt_pow_right (by decide) (show 3*u^10<W by change 3*v<16*v;omega))
  · have heads : R.stageCount+1≤3*v := by omega
    have word : W+1≤17*v := by change 16*v+1≤17*v;omega
    have step : (W+1)*(R.stageCount+1)≤(17*v)*(3*v) := Nat.mul_le_mul word heads
    have num : R.rootsTotal≤chunk := by omega
    have gs : R.groups≤chunk := groups
    have cs : R.chunkBits≤chunk := bits
    have sq : v*v≤v*v*chunk := Nat.le_mul_of_pos_right _ ch
    have vvs : 1≤v*v := Nat.mul_pos vpos vpos
    have more : chunk≤(v*v)*chunk := by simpa using Nat.mul_le_mul_right chunk vvs
    have rows : (W+1)*(R.stageCount+1) ≤ 51*((v*v)*chunk) := calc
      _ ≤ (17*v)*(3*v) := step
      _ = 51*(v*v) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 51 sq
    have total := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add rows (num.trans more)) (lane.trans more)) (gs.trans more)) (cs.trans more)
    calc
      R.publishCost W ≤ _ := publishCost_bound R W
      _ ≤ _ := Nat.mul_le_mul_left 1613 total
      _ = 88715*((v*v)*chunk) := by ring
      _ ≤ 100000*((v*v)*chunk) := Nat.mul_le_mul_right _ (by decide)
      _ = 100000*u^20*chunk := by dsimp only [v]; ring


theorem cursor_root_budget (B : Block F) {u rem low stride cells off tariff : ℕ}
    (shape : PhysicalPinsExpr.Shape) (hu : 40≤u) (levels : B.levels+1≤u)
    (factor : B.allocations.sum≤u) (half : low=u^10/2)
    (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6)
    (groups : 1024*(2*shape.chunks)≤2^(u^10-u^4))
    (bits : shape.bits≤2^(u^10-u^4)) (pairs : 2*shape.halfBits≤2^(3*u^10)) :
    let W := 16*u^10
    let p := Parameters.cursor B u rem low stride cells shape off tariff
    let A := p.archive (2^B.exponent 0) W
    let ss := (B.repeat (u^8)).directory rem p.axes
    let N := p.nodeArchive A ss W
    let R := p.rootArchive A N ss W
    let chunk := 2^(u^10-u^4)
    (R.initialLanes≤R.rootsTotal → R.stageRaw+W*(4*R.stageCount)≤R.header → R.PublishRoom W) ∧
      R.publishCost W≤100000*u^20*chunk := by
  intro W p A ss N R chunk
  obtain ⟨sizes,ticks⟩:=cursor_root_sizes_budget B (rem:=rem) (stride:=stride) (cells:=cells) (off:=off)
    (tariff:=tariff) shape hu levels factor half depth groups bits pairs
  exact ⟨fun enough raw=>physical_publish_room p (2^B.exponent 0) ss W (sizes enough raw),ticks⟩


end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.TickPhysicalABI
open PhysicalStage NavigationDirectory NodePublication TickPhaseModel TickChronology TickAuxiliary
open RAM.TickActiveROM RAM.TickBitRelation RAM.HistoryFactors RAM.Contraction RAM.BitLayout
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] [Fintype F] (B : Block F)
variable {u rem low stride cells tableOffset tariff e : ℕ} (shape : PhysicalPinsExpr.Shape)
local notation "pa" => Parameters.cursor B u rem low stride cells shape tableOffset tariff
local notation "W" => (16*u^10)
local notation "n" => (u^8)
local notation "d" => 2^B.exponent 0
local notation "P" => B.repeat n
local notation "k" => (P).charge+rem
local notation "off" => 1+((k+low)+(k+low))
local notation "A" => (pa).archive d W
variable (hk : 2 ≤ (B.repeat (u^8)).charge+rem)
local notation "X" => B.cursorState hk low off cells
local notation "R" => (P).run rem X
local notation "v" => Fintype.card (X).Base
local notation "ss" => (P).directory rem v
local notation "edges" => (P).finalEdges rem v
local notation "nd" => (pa).nodeArchive A ((P).directory rem (pa).axes) W
local notation "ra" => (pa).rootArchive A nd ((P).directory rem (pa).axes) W
local notation "rs" => nodeLayers (A).K ((P).directory rem (pa).axes) (A).cursor (A).seedLayer
local notation "O" => (A).cursorSeedSites B hk low off cells rfl rfl
local notation "C" => B.charges n rem X
local notation "start" => B.seedWork hk low off cells (2*shape.halfBits) B.cursorCopies (k+low) stride cells
local notation "pay" => B.clippedPairs hk low off cells (2*shape.halfBits)
local notation "budget" => u*(2^(u^10-u^4)+1)
local notation "work" => (A).bootTime ss edges W+(A).seedTime+6+((A).loopTime (u:=u) B n rem X+Archive.terminalTime ((A).terminal ss edges W))

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 10000 in
/-- The actual cursor's three linked blocks preserve the native rejecting and accepting
semantics on the real raw history and supply every operation input of the chosen tick. -/
theorem cursor_machine_admission (field : FieldCode F W) (hu : e+40≤u) (half : low=u^10/2)
    (depth : k+low≤u^10+2*u^6) (degree : d≤u) (slot : off*cells*3≤u^e)
    (alphabet : B.alphabetCap≤u) (levels : B.levels+1≤u) (score : B.costFactors.sum≤u)
    (allocation : B.allocations.sum≤u) (moveWords : fixedMoveWords B≤u)
    (growth : B.widthBase≤u) (factor : B.repeatFactor≤u) (chunk : shape.bits=2^(u^10-u^4))
    (rawBit : ℕ→Bool) (library suffix : List ℕ) (input : Memory W)
    (src : (A).SeedSources ss edges library suffix rawBit input) (window : (A).RawWindow ss rawBit input)
    {clock : Clock} {abi : TickActiveROM.Layout} {span pins H J : ℕ}
    {fit : Fits (TickWeightedBank.shape F pins H J) W}
    (T : Buckets (R).plan ((R).readTerminal (fun z=>z.widthSum)) clock abi.bits (ra).initialLanes span)
    (terminal : HistoryContraction.Plan.Terminal (R).plan ((R).readTerminal (fun z=>z.widthSum))) (t : ℕ) (oa na oc nc : Aux abi.bits)
    (pairFit : 1+abi.capacity+2*T.length terminal (clock.group t)≤abi.bits)
    (net : BitNetwork F pins) (lib : Library net) (hidden : net.internal≤H) (cellCap : net.cells+(H-net.internal)≤J)
    (lut : abi.lut+8*(lib.count+2)≤2^W) (teams team : ℕ) (slotInput : Memory W→Prop)
    (rootWords : let width:=B.cursor_repeat_word hu (by omega : low≤u^10) growth factor slot hk
      let table:=B.recordTable B.alphabetCap W n rem X le_rfl width
      let origin:=(A).startedMemory ss edges library rawBit input n
      ∀ m,(A).Closed B n rem X rawBit table.records origin m →
      ∃ sel : Selection R C O (A).seedData start pay nd ra rs budget m,
        sel.history=terminal.1 ∧ Selection.RootWords (fit:=fit) R C O (A).seedData start pay nd ra rs budget
          T terminal t oa na oc nc pairFit net lib hidden cellCap lut sel teams team slotInput) :
    let width:=B.cursor_repeat_word hu (by omega : low≤u^10) growth factor slot hk
    let table:=B.recordTable B.alphabetCap W n rem X le_rfl width
    let raw:=List.ofFn (fun j : Fin (A).pairCapacity=>rawBit j.val)
    let machine:=(pa).machine («W»:=W) B n rem
    let cell:=T.cellInput (fit:=fit) terminal t oa pairFit net lib hidden cellCap lut
    TickStageSpec.Admission field machine.block machine.publicData (·=input)
      (fun _=>((R).plan.decodeShared table.codes ((R).readTerminal (fun z=>z.widthSum)) (A).pairCapacity raw).isSome)
      (fun _ m=>NavOutput cell (clock.phase t) oa na oc nc slotInput m)
      (work+(nodeTime W (rs).length budget+(ra).publishCost W)) := by
  intro word table raw machine cell
  let origin:=(A).startedMemory ss edges library rawBit input n
  let closed := (A).Closed B n rem X rawBit table.records origin
  have card : v=(pa).axes := Fintype.card_fin k
  have edgesActual : edges=(ra).rootCount*(A).initialDegree :=
    (congrArg (fun axes => (P).finalEdges rem axes) card).trans (Parameters.root_edges pa B n rem W rfl)
  have text : machine = navigation («W»:=W) A nd ra B n rem edges :=
    congrArg (navigation («W»:=W) A nd ra B n rem) edgesActual.symm
  rw [text]
  intro labels registers publicSlots vm
  exact navigation_admission R C O (A).seedData start pay nd ra rs budget T terminal t oa na oc nc
    pairFit net lib hidden cellCap lut field B A n rem edges rfl rfl input
    ((R).plan.decodeShared table.codes ((R).readTerminal (fun z=>z.widthSum)) (A).pairCapacity raw).isSome
    closed work teams team slotInput
    (Parameters.cursor_active B shape hk field hu half depth degree slot alphabet levels score
      allocation moveWords growth factor chunk rawBit library suffix input src window) (fun m valid=>by
      obtain ⟨s,_,ready⟩:=rootWords m valid
      exact ⟨s,ready⟩) vm


end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.TickPhysicalABI
open PhysicalStage NavigationDirectory NodePublication TickPhaseModel TickChronology TickAuxiliary
open RAM.TickActiveROM RAM.TickBitRelation RAM.HistoryFactors RAM.Contraction RAM.BitLayout
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] [Fintype F] (B : Block F)
variable {u rem low stride cells tableOffset tariff e : ℕ} (shape : PhysicalPinsExpr.Shape)
local notation "pa" => Parameters.cursor B u rem low stride cells shape tableOffset tariff
local notation "W" => (16*u^10)
local notation "n" => (u^8)
local notation "d" => 2^B.exponent 0
local notation "P" => B.repeat n
local notation "k" => (P).charge+rem
local notation "off" => 1+((k+low)+(k+low))
local notation "A" => (pa).archive d W
variable (hk : 2 ≤ (B.repeat (u^8)).charge+rem)
local notation "X" => B.cursorState hk low off cells
local notation "R" => (P).run rem X
local notation "v" => Fintype.card (X).Base
local notation "ss" => (P).directory rem v
local notation "edges" => (P).finalEdges rem v
local notation "nd" => (pa).nodeArchive A ((P).directory rem (pa).axes) W
local notation "ra" => (pa).rootArchive A nd ((P).directory rem (pa).axes) W
local notation "rs" => nodeLayers (A).K ((P).directory rem (pa).axes) (A).cursor (A).seedLayer
local notation "O" => (A).cursorSeedSites B hk low off cells rfl rfl
local notation "C" => B.charges n rem X
local notation "start" => B.seedWork hk low off cells (2*shape.halfBits) B.cursorCopies (k+low) stride cells
local notation "pay" => B.clippedPairs hk low off cells (2*shape.halfBits)
local notation "budget" => u*(2^(u^10-u^4)+1)
local notation "work" => (A).bootTime ss edges W+(A).seedTime+6+((A).loopTime (u:=u) B n rem X+Archive.terminalTime ((A).terminal ss edges W))

/-! A rejected native token list exits before publishing any node or root. -/
theorem cursor_machine_reject (field : FieldCode F W) (hu : e+40≤u) (half : low=u^10/2)
    (depth : k+low≤u^10+2*u^6) (degree : d≤u) (slot : off*cells*3≤u^e)
    (alphabet : B.alphabetCap≤u) (levels : B.levels+1≤u) (score : B.costFactors.sum≤u)
    (allocation : B.allocations.sum≤u) (moveWords : fixedMoveWords B≤u)
    (growth : B.widthBase≤u) (factor : B.repeatFactor≤u) (chunk : shape.bits=2^(u^10-u^4))
    (rawBit : ℕ→Bool) (library suffix : List ℕ) (input : Memory W)
    (src : (A).SeedSources ss edges library suffix rawBit input) (window : (A).RawWindow ss rawBit input)
    (bad : let width:=B.cursor_repeat_word hu (by omega : low≤u^10) growth factor slot hk
      let table:=B.recordTable B.alphabetCap W n rem X le_rfl width
      let raw:=List.ofFn (fun j : Fin (A).pairCapacity=>rawBit j.val)
      (R).plan.decodeShared table.codes ((R).readTerminal (fun z=>z.widthSum)) (A).pairCapacity raw=none) :
    let machine:=(pa).machine («W»:=W) B n rem
    TickStageSpec.Admission field machine.block machine.publicData (·=input) (fun _=>False)
      (fun _ _=>False) work := by
  intro machine
  let front:=NavigationPass.active («W»:=W) A B n rem edges
  let tail:=((nd).publish («W»:=W) (rs).length).seq ((ra).publish («W»:=W))
  have dummy : TickStageSpec.Admission field tail.block tail.publicData (fun _=>False) (fun _=>False)
      (fun _ _=>False) 0 := by
    intro pcCount regCount publicCount machine0 pcMap regMap pub exit installed value cfg mem hbegin imposs
    exact imposs.elim
  have card : v=(pa).axes:=Fintype.card_fin k
  have edgeEq : edges=(ra).rootCount*(A).initialDegree :=
    (congrArg (fun axes => (P).finalEdges rem axes) card).trans (Parameters.root_edges pa B n rem W rfl)
  have same : machine=front.seq tail :=
    congrArg (navigation («W»:=W) A nd ra B n rem) edgeEq.symm
  rw [same]
  intro pcCount regCount publicCount machine0 pcMap regMap pub exit installed value cfg mem hbegin hpre
  constructor
  · exact False.elim
  · exact (TickStageSpec.admission_seq field front tail (good:=fun _=>False)
      (Parameters.cursor_active B shape hk field hu half depth degree slot alphabet levels score
        allocation moveWords growth factor chunk rawBit library suffix input src window) dummy
      (fun _ _ h=>h.elim) (fun _ _ _ live _=>by simp [bad] at live)
      machine0 pcMap regMap pub exit installed value cfg mem hbegin hpre).2


end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows RAM.PhysicalProcedure PhysicalStage NavigationDirectory NodePublication
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] (B : Block F) {u rem low stride cells tableOffset tariff e : ℕ}
    (shape : PhysicalPinsExpr.Shape)
local notation "p" => Parameters.cursor B u rem low stride cells shape tableOffset tariff
local notation "W" => (16*u^10)
local notation "n" => (u^8)
local notation "d" => 2^B.exponent 0
local notation "P" => B.repeat n
local notation "k" => (P).charge+rem
local notation "off" => 1+((k+low)+(k+low))
local notation "A" => (p).archive d W
local notation "cur" => ((A).control:Word W)
variable (hk : 2 ≤ (B.repeat (u^8)).charge + rem)
local notation "X" => B.cursorState hk low off cells
local notation "R" => (P).run rem X
local notation "vv" => Fintype.card (X).Base
local notation "ss" => (P).directory rem (p).axes
local notation "edges" => (P).finalEdges rem vv
local notation "N" => (p).nodeArchive A ss W
local notation "root" => (p).rootArchive A N ss W
local notation "rows" => nodeLayers (A).K ss (A).cursor (A).seedLayer
local notation "O" => (A).cursorSeedSites B hk low off cells rfl rfl
local notation "C" => B.charges n rem X
local notation "z" => (((X).maxWidth+1)*B.widthBase^n)
local notation "qtab" => B.recordTable B.alphabetCap W n rem X le_rfl
local notation "start" => B.seedWork hk low off cells (2*shape.halfBits) B.cursorCopies (k+low) stride cells
local notation "pay" => B.clippedPairs hk low off cells (2*shape.halfBits)
local notation "budget" => u*(2^(u^10-u^4)+1)
local notation "amount" => (R).readTerminal (fun Y=>Y.widthSum)

set_option maxRecDepth 10000 in
/-- The physical seed, authenticated stage outputs, and terminal frame determine the
single history, word suffix, root numbering, and literal archive inputs used by the
next two procedures of the native machine. -/
theorem cursor_selection (hu : e+40≤u) (half : low=u^10/2) (depth : k+low≤u^10+2*u^6)
    (fixed : directoryCap B≤u) (fixedTime : 10*nodeWriterBudget B≤u)
    (levels : B.levels+1≤u) (allocation : B.allocations.sum≤u) (slot : off*cells*3≤u^e)
    (peak : B.peakBase≤u) (rate : tariff≤u^e)
    (trace : TraceBitHeader.seedTraceWork low stride cells B.cursorCopies (k+low)≤2^low*u^e)
    (pairLimit : 2*shape.halfBits≤2^(3*u^10)) (word : B.repeatFactor*z<2^W) (bits : ℕ→Bool)
    {origin out : Memory W}
    (closed : (A).Closed B n rem X bits (qtab word).records origin out)
    («meta» : (A).InitialNodeMetadata (X).graph (finCongr (show k=(A).axes from rfl)) (fun _=>(A).relayWidth) origin)
    (lim : (A).Limits u cur ((P).directory rem vv) edges (A).pairCapacity)
    (terminalRoom : (A).TerminalRoom ((P).directory rem vv) edges W)
    (rawMount : Mount (image N (rows).length) (tapeWord N rows) out) :
    let raw:=List.ofFn (fun j : Fin (A).pairCapacity=>bits j.val)
    ∃ (s : Selection R C O (A).seedData start pay N root rows budget out) (suffix : List Bool),
      (R).plan.read (qtab word).codes raw=some (s.history,suffix) ∧ (R).FinalNumbered s.history C O s.path ∧
      s.AtProgram (A).K (finish (A).K ss (A).cursor) (fun Pins=>(P).assembly (Pins:=Pins) rem X) B.publicTemplate ∧
      ∀ v, (R).plan.decodeShared (qtab word).codes amount (A).pairCapacity raw=some v → v.1=s.history := by
  intro raw
  have card : vv=(p).axes := Fintype.card_fin k
  obtain ⟨h,suffix,path,decoded,numbered,stages,wordVisits,actual,terminal,source⟩:=
    cursor_source_rows B shape hk hu half depth fixed levels allocation slot word bits closed «meta» lim terminalRoom
  let xs:=(R).archiveList h C O path (A).seedData
  have eq : records xs=rows := by simpa only [card] using actual
  have L : ((R).finalArchive h C O path).1=lastLayer (A).K ss (A).cursor (A).seedLayer := by simpa only [card] using terminal
  have degree : d≤u := by unfold directoryCap at fixed;omega
  have room := (cursor_run_budget B (rem:=rem) (low:=low) (stride:=stride) (cells:=cells) («off» := tableOffset)
    (tariff:=tariff) shape (by omega) fixed fixedTime levels allocation half depth pairLimit).1
  have tape := cursor_tape_bounds B (rem:=rem) (low:=low) (stride:=stride) (cells:=cells) («off» := tableOffset)
    (tariff:=tariff) shape (by omega) fixed levels allocation half depth pairLimit
  have seeds : State.SeedRows O (A).seedData (N).banks start pay :=
    (A).cursor_seedRows B hk low off cells rfl rfl rfl rfl (N).banks (2*shape.halfBits)
      B.cursorCopies (k+low) stride cells rfl rfl rfl rfl
  have fits := B.cursor_archive_fits (rem:=rem) (total:=2*shape.halfBits) (by omega : 40≤u)
    (by omega : e+2≤u) half.le degree peak slot trace rate hk h
  let input : ArchiveInputs R h C O path (A).seedData N out budget start pay :=
    { room:=by rw [eq];exact room
      tape:=by rw [eq];exact tape
      raw:=by dsimp only;rw [eq];exact rawMount
      source:=by simpa only [card] using source
      initial:=seeds
      fits:=fits }
  have currentCell : (N).banks.current = (A).control := rfl
  have counterCell : (N).counter = (A).control + 3 := rfl
  let s : Selection R C O (A).seedData start pay N root rows budget out :=
    ⟨h,path,input,eq,rfl,congrArg Layer.first L.symm,congrArg Layer.count L.symm,numbered,(A).K,
      (finish (A).K ss (A).cursor).header,(finish (A).K ss (A).cursor).heap,by
        simpa only [currentCell, counterCell, card] using stages⟩
  refine ⟨s,suffix,decoded,numbered,⟨⟨rfl,rfl,rfl⟩,?_⟩,?_⟩
  · intro Pins L
    change (R).WordVisits
      (RecordedWordStep (A).K ((N).banks.current : Word W) ((N).counter : Word W)
        (finish (A).K ss (A).cursor).header (finish (A).K ss (A).cursor).heap out Pins B.publicTemplate)
      h ((P).assembly rem X).steps L C O path
    simpa only [currentCell, counterCell, card] using wordVisits Pins L
  rintro ⟨picked,wire⟩ dec
  let pad:=List.replicate ((A).pairCapacity-((R).plan.write (qtab word).codes picked).length-amount picked) false
  have same : some (h,suffix)=some (picked,List.ofFn wire++pad) := calc
    some (h,suffix)=(R).plan.read (qtab word).codes raw:=decoded.symm
    _=(R).plan.read (qtab word).codes ((R).plan.encodeShared (qtab word).codes amount (A).pairCapacity ⟨picked,wire⟩):=
      congrArg ((R).plan.read (qtab word).codes) ((R).plan.encode_decode (qtab word).codes amount (A).pairCapacity raw _ dec).symm
    _=_:=(R).plan.read_write (qtab word).codes picked _
  exact (congrArg Prod.fst (Option.some.inj same)).symm


end
end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.TickPhysicalABI
open PhysicalStage NavigationDirectory NodePublication TickPhaseModel TickChronology TickAuxiliary
open RAM.TickActiveROM RAM.TickBitRelation RAM.HistoryFactors RAM.Contraction RAM.BitLayout
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] [Fintype F] (B : Block F)
variable {u rem low stride cells tableOffset tariff e : ℕ} (shape : PhysicalPinsExpr.Shape)
local notation "pa" => Parameters.cursor B u rem low stride cells shape tableOffset tariff
local notation "W" => (16*u^10)
local notation "n" => (u^8)
local notation "d" => 2^B.exponent 0
local notation "P" => B.repeat n
local notation "k" => (P).charge+rem
local notation "off" => 1+((k+low)+(k+low))
local notation "A" => (pa).archive d W
variable (hk : 2 ≤ (B.repeat (u^8)).charge+rem)
local notation "X" => B.cursorState hk low off cells
local notation "R" => (P).run rem X
local notation "v" => Fintype.card (X).Base
local notation "ss" => (P).directory rem v
local notation "edges" => (P).finalEdges rem v
local notation "nd" => (pa).nodeArchive A ((P).directory rem (pa).axes) W
local notation "ra" => (pa).rootArchive A nd ((P).directory rem (pa).axes) W
local notation "rs" => nodeLayers (A).K ((P).directory rem (pa).axes) (A).cursor (A).seedLayer
local notation "O" => (A).cursorSeedSites B hk low off cells rfl rfl
local notation "C" => B.charges n rem X
local notation "start" => B.seedWork hk low off cells (2*shape.halfBits) B.cursorCopies (k+low) stride cells
local notation "pay" => B.clippedPairs hk low off cells (2*shape.halfBits)
local notation "budget" => u*(2^(u^10-u^4)+1)
local notation "work" => (A).bootTime ss edges W+(A).seedTime+6+((A).loopTime (u:=u) B n rem X+Archive.terminalTime ((A).terminal ss edges W))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
/-- Physical source and root-word specialization for an actually decoded terminal history. -/
theorem cursor_selected_tick (field : FieldCode F W) (hu : e+40≤u) (half : low=u^10/2)
    (depth : k+low≤u^10+2*u^6) (degree : d≤u) (slot : off*cells*3≤u^e)
    (alphabet : B.alphabetCap≤u) (levels : B.levels+1≤u) (score : B.costFactors.sum≤u)
    (allocation : B.allocations.sum≤u) (moveWords : fixedMoveWords B≤u)
    (growth : B.widthBase≤u) (factor : B.repeatFactor≤u) (chunk : shape.bits=2^(u^10-u^4))
    (rawBit : ℕ→Bool) (library suffix : List ℕ) (input : Memory W)
    (src : (A).SeedSources ss edges library suffix rawBit input) (window : (A).RawWindow ss rawBit input)
    {clock : Clock} {abi : TickActiveROM.Layout} {span pins H J : ℕ}
    {fit : Fits (TickWeightedBank.shape F pins H J) W}
    (T : Buckets (R).plan ((R).readTerminal (fun z=>z.widthSum)) clock abi.bits (ra).initialLanes span)
    (terminal : HistoryContraction.Plan.Terminal (R).plan ((R).readTerminal (fun z=>z.widthSum))) (t : ℕ) (oa na oc nc : Aux abi.bits)
    (pairFit : 1+abi.capacity+2*T.length terminal (clock.group t)≤abi.bits)
    (net : BitNetwork F pins) (lib : Library net) (hidden : net.internal≤H) (cellCap : net.cells+(H-net.internal)≤J)
    (lut : abi.lut+8*(lib.count+2)≤2^W) (teams team : ℕ)
    (fixed : directoryCap B≤u) (fixedTime : 10*nodeWriterBudget B≤u)
    (peak : B.peakBase≤u) (rate : tariff≤u^e)
    (trace : TraceBitHeader.seedTraceWork low stride cells B.cursorCopies (k+low)≤2^low*u^e)
    (pairLimit : 2*shape.halfBits≤2^(3*u^10))
    (words : let bound:=B.cursor_repeat_word hu (by omega : low≤u^10) growth factor slot hk
      let table:=B.recordTable B.alphabetCap W n rem X le_rfl bound
      let origin:=(A).startedMemory ss edges library rawBit input n
      let closed:=(A).Closed B n rem X rawBit table.records origin
      let raw:=List.ofFn (fun j : Fin (A).pairCapacity=>rawBit j.val)
      (R).plan.decodeShared table.codes ((R).readTerminal (fun z=>z.widthSum)) (A).pairCapacity raw=some terminal ∧
      (∀ m,closed m→Mount (image nd (rs).length) (tapeWord nd rs) m) ∧
      ∀ (m : Memory W), closed m→∀ s : Selection R C O (A).seedData start pay nd ra rs budget m,
        s.history=terminal.1 → s.AtProgram (A).K (finish (A).K ((P).directory rem (pa).axes) (A).cursor) (fun Pins=>(P).assembly (Pins:=Pins) rem X) B.publicTemplate →
        ∀ out : Memory W,out=state nd (program ((R).archiveList s.history C O s.path (A).seedData)) m (rs).length →
        (O).Charged (ra).nodeBank (natural out) start pay →
        ∀ stored : (R).ArchiveRowsStored (ra).nodeBank (natural out) s.history C O s.path,
        let ns:=RootArchive.nodesOfRun ra R s.history C O s.path out stored s.zero s.first s.card start pay
        RootInputs ra T terminal t oa na oc nc (T.cellInput (fit:=fit) terminal t oa pairFit net lib hidden cellCap lut)
          ns teams rs out team) :
    let bound:=B.cursor_repeat_word hu (by omega : low≤u^10) growth factor slot hk
    let table:=B.recordTable B.alphabetCap W n rem X le_rfl bound
    let origin:=(A).startedMemory ss edges library rawBit input n
    let raw:=List.ofFn (fun j : Fin (A).pairCapacity=>rawBit j.val)
    let closed:=(A).Closed B n rem X rawBit table.records origin
    let accepted : Option (HistoryContraction.Plan.Terminal (R).plan ((R).readTerminal (fun z=>z.widthSum))) :=
      (R).plan.decodeShared table.codes ((R).readTerminal (fun z=>z.widthSum)) (A).pairCapacity raw
    let machine:=(pa).machine («W»:=W) B n rem
    let cell:=T.cellInput (fit:=fit) terminal t oa pairFit net lib hidden cellCap lut
    let next:=CursorSlot (fit:=fit) R C O (A).seedData start pay nd ra rs budget T terminal t oa na oc nc
      pairFit net lib hidden cellCap lut closed (·=terminal.1) teams team
        (fun _ s=>s.AtProgram (A).K (finish (A).K ((P).directory rem (pa).axes) (A).cursor) (fun Pins=>(P).assembly (Pins:=Pins) rem X) B.publicTemplate)
    TickStageSpec.Admission field machine.block machine.publicData (·=input) (fun _=>accepted.isSome)
      (fun _ out=>NavOutput cell (clock.phase t) oa na oc nc next out)
      (work+(nodeTime W (rs).length budget+(ra).publishCost W)) := by
  intro bound table origin raw closed accepted machine cell next
  have seedMeta:=Parameters.cursor_started_nodes B shape hk hu half depth degree slot alphabet levels score
    rawBit library suffix input src
  have facts := words
  obtain ⟨valid,mount,root⟩:=facts
  have card : v=(pa).axes:=Fintype.card_fin k
  have limits : (A).Limits u ((A).control:Word W) ss edges (A).pairCapacity := by
    rw [card]
    exact Parameters.cursor_limits B shape (by omega) levels allocation score alphabet half depth chunk _
  have termRoom : (A).TerminalRoom ss edges W := by
    have ageBound : 40 ≤ u := by omega
    have axesBound : (pa).axes ≤ u^10+2*u^6 := (Nat.le_add_right k low).trans depth
    have space := (pa).terminal_space B n rem ageBound degree axesBound rfl
    rw [card] at limits ⊢
    exact (space limits window.old window.fresh).1
  apply cursor_machine_admission B shape hk field hu half depth degree slot alphabet levels score allocation
    moveWords growth factor chunk rawBit library suffix input src window T terminal t oa na oc nc pairFit
    net lib hidden cellCap lut teams team next
  intro selectedWidth selectedTable selectedOrigin m had
  change closed m at had
  obtain ⟨s,tail,read,number,profile,det⟩:=cursor_selection B shape hk hu half depth fixed fixedTime
    levels allocation slot peak rate trace pairLimit bound rawBit had seedMeta limits termRoom (mount m had)
  have same:= (det terminal valid).symm
  refine ⟨s,same,?_⟩
  exact Selection.rootWords_of_inputs R C O (A).seedData start pay nd ra rs budget T terminal t oa na oc nc
    pairFit net lib hidden cellCap lut s closed (·=terminal.1) had same teams team (root m had s same profile) _ profile


end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation.RootABI

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open PhysicalStage NavigationDirectory NodePublication TickPhaseModel TickChronology TickAuxiliary
open RAM.TickActiveROM RAM.TickPhysicalABI RAM.TickBitRelation RAM.TickIntervalCursor
open RAM.HistoryFactors RAM.Contraction RAM.BitLayout
open scoped Classical Fin.CommRing
noncomputable section
variable {W : ℕ} {F : Type} [Field F] [Fintype F]

/-- The portions of the root scan ABI read at fixed locations in the mounted tick. -/
structure Fields (a : RootArchive) (A : TickActiveROM.Layout) (W : ℕ) : Prop where
  sCount : A.intervalCount=TickWorkspace.base a.age 6
  sTable : A.intervalTable=TickWorkspace.base a.age 5
  sMap : A.intervalMap=TickWorkspace.base a.age 7
  sCounters : A.groupCounts=TickWorkspace.base a.age 8
  clkFit : A.clockWords<2^W
  clo : A.clockWords+3<a.protectedBelow
  ctl : A.control+3<a.protectedBelow
  oaFit : A.oldAux+A.bits≤a.protectedBelow
  naFit : A.newAux+A.bits≤a.protectedBelow
  ocFit : A.oldChunk+A.bits≤a.protectedBelow
  ncFit : A.newChunk+A.bits≤a.protectedBelow
  protectedFit : a.protectedBelow<2^W

theorem parameter_fields {pins H J : ℕ} (p : Parameters) (degree : ℕ) (ss : List Stage)
    (W chunk teams cap q nt ns np : ℕ) {fit : Fits (TickWeightedBank.shape F pins H J) W}
    (bounds : WordBounds (TickPhysicalABI.mounted p.age chunk teams cap q nt ns np) fit) :
    Fields (RootArchive.parameterArchive p degree ss W)
      (TickPhysicalABI.mounted p.age chunk teams cap q nt ns np) W := by
  let a:=RootArchive.parameterArchive p degree ss W
  let A:=TickPhysicalABI.mounted p.age chunk teams cap q nt ns np
  have low : A.bounds≤a.protectedBelow := by
    rw [RootArchive.parameter_protected p degree W ss]
    change 3*TickWorkspace.stride p.age≤6*TickWorkspace.stride p.age
    omega
  have c:=bounds.ctrl
  have k:=bounds.clk
  have b:=bounds.bounds
  have r:=bounds.requests
  change A.control+4≤A.clockWords at c
  change A.clockWords+4≤A.bounds at k
  change A.bounds+4≤A.auxRequest at b
  change A.auxRequest+8*A.bits<2^W at r
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,?_,bounds.oldAux.trans low,bounds.newAux.trans low,
    bounds.oldChunk.trans low,bounds.newChunk.trans low,?_⟩
  · change A.clockWords<2^W; omega
  · change A.clockWords+3<a.protectedBelow; omega
  · change A.control+3<a.protectedBelow; omega
  · rw [RootArchive.parameter_protected p degree W ss]
    have size := bounds.meta
    change 10*TickWorkspace.stride p.age+4*J≤2^W at size
    change 6*TickWorkspace.stride p.age<2^W
    have positive : 0<TickWorkspace.stride p.age := by unfold TickWorkspace.stride; positivity
    omega

theorem clock_numeric (clock : Clock) (t chunkWidth : ℕ)
    (lastFit : clock.last<2^W) (stepFit : t<2^W) (totalFit : clock.chunks*chunkWidth<2^W) :
    clock.groups<2^W ∧ clock.group t<2^W ∧ (chunk clock t).val*chunkWidth+chunkWidth<2^W := by
  have pos:=clock.duration_pos
  have limit:=clock.fits
  have duration:=Nat.le_mul_of_pos_right clock.groups pos
  have ordinal : clock.group t≤t := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have endChunk:=Nat.mul_le_mul_right chunkWidth (chunk clock t).isLt
  rw [Nat.succ_mul] at endChunk
  exact ⟨by omega,ordinal.trans_lt stepFit,endChunk.trans_lt totalFit⟩


end
end ThreeFlat.Diagonal.NavigationPass.NativeNavigation.RootABI

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation.RootABI

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open PhysicalStage NavigationDirectory NodePublication TickPhaseModel TickChronology TickAuxiliary
open RAM.TickActiveROM RAM.TickPhysicalABI RAM.TickBitRelation RAM.TickIntervalCursor
open RAM.HistoryFactors RAM.Contraction RAM.BitLayout
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] (B : Block F) {u rem low stride cells off tariff : ℕ}
    (shape : PhysicalPinsExpr.Shape)
local notation "p" => Parameters.cursor B u rem low stride cells shape off tariff
local notation "W" => 16*u^10
local notation "P" => B.repeat (u^8)
local notation "k" => (P).charge+rem
local notation "d" => 2^B.exponent 0
local notation "A" => (p).archive d W
local notation "ss" => (P).directory rem (p).axes
local notation "N" => (p).nodeArchive A ss W
local notation "root" => (p).rootArchive A N ss W
variable (hk : 2 ≤ (B.repeat (u^8)).charge + rem)
local notation "X" => B.cursorState hk low (1+((k+low)+(k+low))) cells
local notation "R" => (P).run rem X
local notation "bits" => (R).readTerminal (fun z=>z.widthSum)
variable (clock : Clock) (positive : 0<clock.groups) (total : clock.chunks=2*shape.chunks)
    (cover : 2*shape.halfBits ≤ 2^(((B.repeat (u^8)).charge+rem)+low))
local notation "T" => Parameters.cursorBuckets B u rem low stride cells off tariff shape hk clock positive total cover
variable (teams cap : ℕ)
local notation "abi" => TickPhysicalABI.mounted u shape.bits teams cap shape.advice shape.teamBits shape.timeBits shape.parameterBits

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1200000 in
/-- Every address, array, and comparison for the actual scheduled tick's scan has
the stated machine-word range. The lane count and row allocation use the physical
program's own charge and the terminal from its common bucket bank. -/
theorem cursor_limits {pins H J : ℕ} {fit : Fits (TickWeightedBank.shape F pins H J) W}
    (hu : 40≤u) (depth : k+low≤u^10+2*u^6) (chunkSize : shape.bits≤2^(u^10-u^4))
    (groupCount : clock.groups=1024*(2*shape.chunks)) (lastTick : clock.last+1=2^(u^6))
    (bounds : WordBounds abi fit) (v : HistoryContraction.Plan.Terminal (R).plan bits) (t : ℕ) (tick : t<2^(u^6))
    (oa : Aux (abi).bits) (pairFit : 1+(abi).capacity+2*(T).length v (clock.group t)≤(abi).bits)
    (net : BitNetwork F pins) (lib : Library net) (hidden : net.internal≤H) (cellsCap : net.cells+(H-net.internal)≤J)
    (lut : (abi).lut+8*(lib.count+2)≤2^W) :
    RootLimits root T v t ((T).cellInput («A»:=abi) (fit:=fit) v t oa pairFit net lib hidden cellsCap lut) := by
  have fixed:=parameter_fields p d ss W shape.bits teams cap shape.advice shape.teamBits shape.timeBits
    shape.parameterBits bounds
  have pow : u^6≤u^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have pos : 0<u^10 := Nat.pow_pos (by omega : 0 < u)
  have duration : 2^(u^6)≤ (2:ℕ)^W := Nat.pow_le_pow_right (by decide) (by omega)
  have countEq : (root).totalPairs=clock.chunks*(abi).bits := by
    change 2*(shape.chunks*shape.bits)=clock.chunks*shape.bits
    rw [total,Nat.mul_assoc]
  have mass : clock.chunks*(abi).bits<2^W := by
    rw [←countEq]
    exact cover.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  have time := clock_numeric («W»:=W) clock t (abi).bits (by omega) (tick.trans_le duration) mass
  have ng : (root).groups=clock.groups := groupCount.symm
  exact ⟨fixed.sCount,fixed.sTable,fixed.sMap,fixed.sCounters,rfl,countEq,rfl,ng,(by rw [ng]; exact time.1),
    cursor_root_space B (rem:=rem) (low:=low) (stride:=stride) (cells:=cells) (off:=off) (tariff:=tariff)
      shape hu depth,bounds,cursor_root_scan_ranges B shape hu depth chunkSize teams cap shape.advice
        shape.teamBits shape.timeBits shape.parameterBits T v,
    time.2.2,time.2.1,fixed.clkFit,fixed.clo,fixed.ctl,fixed.oaFit,fixed.naFit,fixed.ocFit,fixed.ncFit⟩


end
end ThreeFlat.Diagonal.NavigationPass.NativeNavigation.RootABI

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.NavigationNodeRows PhysicalStage NavigationDirectory NodePublication
open TickChronology RAM.TickPhysicalABI ApproximateImage
open scoped Classical Fin.CommRing
noncomputable section

private theorem stride_of_base_zero {p u : ℕ} (h : p ≤ TickWorkspace.base u 0) :
    p ≤ TickWorkspace.stride u := by
  simpa only [TickWorkspace.base, Nat.zero_add, Nat.one_mul] using h

private theorem raw_prefix_below_stride {u a teams capacity d nt ns np : ℕ}
    (pins : 2 + pinCount d nt ns np a ≤ (TickPhysicalABI.mounted u a teams capacity d nt ns np).control) :
    2 + d + nt + ns + np ≤ TickWorkspace.stride u := by
  have bound := stride_of_base_zero (p := 2 + pinCount d nt ns np a) (u := u) pins
  unfold pinCount at bound
  omega


private theorem root_pin_ends (q nt ns np a bound : ℕ)
    (pinLow : 2 + pinCount q nt ns np a ≤ bound) :
    let first := 2+q+nt+ns+np
    first ≤ bound ∧ first+a ≤ bound ∧ first+a+a ≤ bound ∧
      first+2*a+a ≤ bound ∧ first+3*a+a ≤ bound := by
  dsimp only
  unfold pinCount at pinLow
  omega

private theorem root_clock_ends (u w : ℕ) (age : 40 ≤ u)
    (pointer : TickWorkspace.base u 40 < 2^w) :
    TickWorkspace.base u 0 + 4 ≤ TickWorkspace.base u 1 ∧
    TickWorkspace.base u 0 + 4 ≤ TickWorkspace.base u 20 ∧
    TickWorkspace.base u 1 + 4 ≤ TickWorkspace.base u 20 ∧
    TickWorkspace.base u 1 + 4 < 2^w := by
  have power : u ≤ 2^(u^10) :=
    (Nat.le_self_pow (by decide : 10≠0) u).trans Nat.lt_two_pow_self.le
  have width : 4 ≤ TickWorkspace.stride u :=
    (show 4 ≤ u by omega).trans (power.trans (Nat.le_self_pow (by decide : 4≠0) _))
  have a := TickWorkspace.apart (u:=u) (by decide : 0<1)
  have b := TickWorkspace.apart (u:=u) (by decide : 1<20)
  have c := TickWorkspace.apart (u:=u) (by decide : 20<40)
  omega

private theorem root_memory_of_frame {w : ℕ} (layout : TickActiveROM.Layout) (archive : RootArchive)
    (rows : List Layers) (clock : Clock) (step team limit : ℕ) (m input : Memory w)
    (oa na oc nc : Fin layout.bits → Bool)
    (header : Mount archive.headerImage archive.headerData m)
    (stages : Mount archive.stageImage (archive.stageData rows) m)
    (keep : ∀ x, x < limit → m x = input x)
    (ctrl : layout.control + 4 ≤ limit) (clk : layout.clockWords + 4 ≤ limit)
    (ends : layout.oldAux + layout.bits ≤ layout.control ∧ layout.newAux + layout.bits ≤ layout.control ∧
      layout.oldChunk + layout.bits ≤ layout.control ∧ layout.newChunk + layout.bits ≤ layout.control)
    (clocks : TickPhysicalABI.Inputs layout clock input team step)
    (old : ∀ i : Fin layout.bits, input (layout.oldAux+i.val) = TickBitRelation.bitWord w (oa i))
    (fresh : ∀ i : Fin layout.bits, input (layout.newAux+i.val) = TickBitRelation.bitWord w (na i))
    (oldC : ∀ i : Fin layout.bits, input (layout.oldChunk+i.val) = TickBitRelation.bitWord w (oc i))
    (newC : ∀ i : Fin layout.bits, input (layout.newChunk+i.val) = TickBitRelation.bitWord w (nc i)) :
    RootMemory (W:=w) (c:=clock) (A:=layout) archive step oa na oc nc rows m team := by
  have readAt {start count : ℕ} (fits : start+count ≤ limit) (i : Fin count) :
      m (start+i.val) = input (start+i.val) :=
    keep _ ((Nat.add_lt_add_left i.isLt start).trans_le fits)
  have low : layout.control ≤ limit := (Nat.le_add_right layout.control 4).trans ctrl
  exact ⟨header,stages,⟨fun i => (readAt ctrl i).trans (clocks.1 i),
    fun i => (readAt clk i).trans (clocks.2 i)⟩,
    fun i => (readAt (ends.1.trans low) i).trans (old i),
    fun i => (readAt (ends.2.1.trans low) i).trans (fresh i),
    fun i => (readAt (ends.2.2.1.trans low) i).trans (oldC i),
    fun i => (readAt (ends.2.2.2.trans low) i).trans (newC i)⟩

private theorem root_memory_at_rows {w : ℕ} (nodes : NodeArchive) (archive : RootArchive)
    (layout : TickActiveROM.Layout) (clock : Clock) (step team : ℕ)
    (oa na oc nc : Fin layout.bits → Bool) (rows : List Layers) (out : Memory w)
    (initial : Mount (image nodes rows.length) (tapeWord nodes rows) out)
    (frames : ∀ Q : Program rows, RootMemory (W:=w) (c:=clock) (A:=layout)
      archive step oa na oc nc rows (state (W:=w) (rows:=rows) nodes Q out rows.length) team) :
    Mount (image nodes rows.length) (tapeWord nodes rows) out ∧
      ∀ {ls : List Layers}, ls = rows → ∀ Q : Program ls, RootMemory (W:=w) (c:=clock) (A:=layout)
        archive step oa na oc nc rows (state (W:=w) (rows:=ls) nodes Q out rows.length) team := by
  refine ⟨initial, ?_⟩
  intro ls eq Q
  subst ls
  exact frames Q

variable {F : Type} [Field F] [Fintype F] (B : Block F)
variable {u rem low stride cells off tariff : ℕ} (shape : PhysicalPinsExpr.Shape)
local notation "pa" => Parameters.cursor B u rem low stride cells shape off tariff
local notation "W" => (16*u^10)
local notation "n" => (u^8)
local notation "d" => (2^B.exponent 0)
local notation "P" => B.repeat n
local notation "k" => (P).charge+rem
section
variable (initialState : PhysicalStage.State (2^B.exponent 0) ((B.repeat (u^8)).charge+rem))
local notation "X" => initialState
local notation "vv" => Fintype.card (X).Base
local notation "ss" => (P).directory rem vv
local notation "edges" => (P).finalEdges rem vv
local notation "A" => (pa).archive d W
local notation "N" => (pa).nodeArchive A ss W
local notation "R" => (pa).rootArchive A N ss W
local notation "rs" => nodeLayers (A).K ss (A).cursor (A).seedLayer
local notation "lib" => Parameters.gridWords B u
local notation "suffix" => nodeTape (N).banks (N).headerBase rs++(List.ofFn (fun j : Fin 22=>(R).word j)++stageTape rs)
variable {teams : ℕ} (clock : Clock) (team t : ℕ) (D : Fin shape.advice→Bool)
variable (par : Fin shape.parameterBits→Bool) (oa na oc nc : Fin shape.bits→Bool)
local notation "abi" => mounted u shape.bits teams (shape.bits/2) shape.advice shape.teamBits shape.timeBits shape.parameterBits
local notation "pins" => fields D (digits team shape.teamBits) (digits t shape.timeBits) par oa na oc nc
local notation "entry" => TickNavigationEntry.input abi clock team t (TickMountedPins.memory (w:=W) pins)
local notation "bits" => entryHistory (clock.phase t) oa na
local notation "cur" => ((A).control:Word W)

set_option maxRecDepth 15000 in
set_option maxHeartbeats 1600000 in
/-- The S41 input of the native node scan, all S42 and stage input words, the four signed
boundary vectors and both clock vectors at the actual RAM emitted by that scan. -/
private theorem visit_closed_root_memory (card : vv = (pa).axes)
    (hu : 40≤u) (degree : d≤u) (half : low=u^10/2) (depth : k+low≤u^10+2*u^6)
    (alphabet : B.alphabetCap≤u) (levels : B.levels+1≤u) (score : B.costFactors.sum≤u)
    {budget : ℕ} (room : RunBounds W N rs budget) (root : RootArchive.PublishRoom R W)
    (limits : (A).Limits u cur ss edges (A).pairCapacity) (out : Memory W)
    (src : (A).SeedSources ss edges lib suffix bits entry)
    (E : ((P).run rem X).Records)
    (closed : (A).Closed B n rem X bits E ((A).startedMemory ss edges lib bits entry n) out)
    (fit : off+W*(lib++(pa).staticWords B n rem W).length ≤ shape.parameterBits)
    (pinLow : 2+pinCount shape.advice shape.teamBits shape.timeBits shape.parameterBits shape.bits≤(abi).control) :
    Mount (image N (rs).length) (tapeWord N rs) out ∧
    ∀ {ls : List Layers},ls=rs→∀ Q : Program ls,
      RootMemory («W»:=W) (c:=clock) («A»:=abi) R t oa na oc nc rs (state («W»:=W) (rows:=ls) N Q out (rs).length) team := by
  have fieldsFit := root_pin_ends shape.advice shape.teamBits shape.timeBits shape.parameterBits shape.bits
    ((abi).control) pinLow
  have lowBound := stride_of_base_zero (u:=u) (p:=2+shape.advice+shape.teamBits+shape.timeBits+shape.parameterBits) fieldsFit.1
  have mounts := cursor_closed_mounts (u:=u) (rem:=rem) (low:=low) (stride:=stride) (cells:=cells)
    («off»:=off) (tariff:=tariff) B shape X card hu degree half depth alphabet levels score room root limits
    bits entry out src E closed fit lowBound
  have protect := (cursor_closed_low (u:=u) (rem:=rem) (low:=low) (stride:=stride) (cells:=cells)
    («off»:=off) (tariff:=tariff) B shape X card hu degree half depth alphabet levels score room limits
    bits entry out src E closed).2
  have gaps := root_clock_ends u W hu room.pointerSize
  have readings := mounted_boundaries («W»:=W) (u:=u) (teams:=teams) (capacity:=shape.bits/2)
    (q:=shape.advice) (nt:=shape.teamBits) (ns:=shape.timeBits) (np:=shape.parameterBits) (a:=shape.bits)
    clock D team t par oa na oc nc pinLow gaps.1 gaps.2.2.2
  refine root_memory_at_rows (w:=W) N R abi clock t team oa na oc nc rs out mounts.1 ?_
  intro Q
  exact root_memory_of_frame (w:=W) abi R rs clock t team (A).seed (state («W»:=W) N Q out (rs).length)
    entry oa na oc nc (mounts.2 Q).1 (mounts.2 Q).2 (protect Q) gaps.2.1 gaps.2.2.1 fieldsFit.2
    readings.1 readings.2.1 readings.2.2.1 readings.2.2.2.1 readings.2.2.2.2.1


end

variable (hk : 2 ≤ (B.repeat (u^8)).charge + rem)
local notation "X" => B.cursorState hk low (1+((k+low)+(k+low))) cells
local notation "vv" => Fintype.card (X).Base
local notation "ss" => (P).directory rem vv
local notation "edges" => (P).finalEdges rem vv
local notation "A" => (pa).archive d W
local notation "N" => (pa).nodeArchive A ss W
local notation "R" => (pa).rootArchive A N ss W
local notation "rs" => nodeLayers (A).K ss (A).cursor (A).seedLayer
local notation "lib" => Parameters.gridWords B u
local notation "suffix" => nodeTape (N).banks (N).headerBase rs++(List.ofFn (fun j : Fin 22=>(R).word j)++stageTape rs)
variable {teams : ℕ} (clock : Clock) (team t : ℕ) (D : Fin shape.advice→Bool)
variable (par : Fin shape.parameterBits→Bool) (oa na oc nc : Fin shape.bits→Bool)
local notation "abi" => mounted u shape.bits teams (shape.bits/2) shape.advice shape.teamBits shape.timeBits shape.parameterBits
local notation "pins" => fields D (digits team shape.teamBits) (digits t shape.timeBits) par oa na oc nc
local notation "entry" => TickNavigationEntry.input abi clock team t (TickMountedPins.memory (w:=W) pins)
local notation "bits" => entryHistory (clock.phase t) oa na
local notation "cur" => ((A).control:Word W)

local notation "S" => (P).directory rem (pa).axes
local notation "nodes" => (pa).nodeArchive A S W
local notation "rootABI" => (pa).rootArchive A nodes S W
local notation "layers" => nodeLayers (A).K S (A).cursor (A).seedLayer
local notation "tailTape" => nodeTape (nodes).banks (nodes).headerBase layers++
  (List.ofFn (fun j : Fin 22=>(rootABI).word j)++stageTape layers)

set_option maxRecDepth 15000 in
set_option maxHeartbeats 1600000 in
/-- The S41 input of the native node scan, all S42 and stage input words, the four signed
boundary vectors and both clock vectors at the actual RAM emitted by that scan. -/
theorem cursor_closed_root_memory
    (hu : 40≤u) (degree : d≤u) (half : low=u^10/2) (depth : k+low≤u^10+2*u^6)
    (alphabet : B.alphabetCap≤u) (levels : B.levels+1≤u) (score : B.costFactors.sum≤u)
    {budget : ℕ} (room : RunBounds W nodes layers budget) (root : RootArchive.PublishRoom rootABI W)
    (limits : (A).Limits u cur ss edges (A).pairCapacity) (out : Memory W)
    (src : (A).SeedSources ss edges lib tailTape bits entry)
    (E : ((P).run rem X).Records)
    (closed : (A).Closed B n rem X bits E ((A).startedMemory ss edges lib bits entry n) out)
    (fit : off+W*(lib++(pa).staticWords B n rem W).length ≤ shape.parameterBits)
    (pinLow : 2+pinCount shape.advice shape.teamBits shape.timeBits shape.parameterBits shape.bits≤(abi).control) :
    Mount (image nodes (layers).length) (tapeWord nodes layers) out ∧
    ∀ {ls : List Layers},ls=layers→∀ Q : Program ls,
      RootMemory («W»:=W) (c:=clock) («A»:=abi) rootABI t oa na oc nc layers (state («W»:=W) (rows:=ls) nodes Q out (layers).length) team := by
  have card : vv=(pa).axes:=Fintype.card_fin k
  have native := visit_closed_root_memory (u:=u) (rem:=rem) (low:=low) (stride:=stride) (cells:=cells)
    («off»:=off) (tariff:=tariff) (teams:=teams) (budget:=budget) B shape X clock team t D par oa na oc nc
    card hu degree half depth alphabet levels score
  simp only [card] at native limits src closed
  exact native room root limits out src E closed fit pinLow


end
end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.TickPhysicalABI
open PhysicalStage NavigationDirectory NodePublication TickPhaseModel TickChronology TickAuxiliary
open RAM.TickActiveROM RAM.TickBitRelation RAM.HistoryFactors RAM.Contraction RAM.BitLayout
open scoped Classical Fin.CommRing
noncomputable section

variable {F : Type} [Field F] [Fintype F] (B : Block F)
variable {u rem low stride cells off tariff e Aexp : ℕ} (shape : PhysicalPinsExpr.Shape)
local notation "pa" => Parameters.cursor B u rem low stride cells shape off tariff
local notation "W" => (16*u^10)
local notation "n" => (u^8)
local notation "d" => 2^B.exponent 0
local notation "P" => B.repeat n
local notation "k" => (P).charge+rem
local notation "offsets" => 1+((k+low)+(k+low))
local notation "A" => (pa).archive d W
variable (hk : 2 ≤ (B.repeat (u^8)).charge+rem)
local notation "X" => B.cursorState hk low offsets cells
local notation "R" => (P).run rem X
local notation "ss" => (P).directory rem (pa).axes
local notation "nd" => (pa).nodeArchive A ss W
local notation "ra" => (pa).rootArchive A nd ss W
local notation "rs" => nodeLayers (A).K ss (A).cursor (A).seedLayer
local notation "O" => (A).cursorSeedSites B hk low offsets cells rfl rfl
local notation "C" => B.charges n rem X
local notation "start" => B.seedWork hk low offsets cells (2*shape.halfBits) B.cursorCopies (k+low) stride cells
local notation "pay" => B.clippedPairs hk low offsets cells (2*shape.halfBits)
local notation "budget" => u*(2^(u^10-u^4)+1)
local notation "bitCount" => (R).readTerminal (fun z=>z.widthSum)
variable (clock : Clock) (positive : 0<clock.groups) (total : clock.chunks=2*shape.chunks)
    (cover : 2*shape.halfBits≤2^(((B.repeat (u^8)).charge+rem)+low))
local notation "buckets" => Parameters.cursorBuckets B u rem low stride cells off tariff shape hk clock positive total cover
variable (teams cap : ℕ)
local notation "abi" => TickPhysicalABI.mounted u shape.bits teams cap shape.advice shape.teamBits shape.timeBits shape.parameterBits
local notation "teamSlots" => clock.evaluateTicks*2^(u^3)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
set_option cleanup.letToHave false in
/-- At a decoded leaf, assign the real cursor roots by their charged physical order,
using the very same greedy groups that partition the literal clipped source lanes. -/
theorem cursor_root_inputs {pins H J : ℕ} {fit : Fits (TickWeightedBank.shape F pins H J) W}
    (terminal : HistoryContraction.Plan.Terminal (R).plan bitCount) (t : ℕ) (oa na oc nc : Aux (abi).bits)
    (pairFit : 1+(abi).capacity+2*(buckets).length terminal (clock.group t)≤(abi).bits)
    (net : BitNetwork F pins) (lib : Library net) (hidden : net.internal≤H)
    (cellCap : net.cells+(H-net.internal)≤J) (lut : (abi).lut+8*(lib.count+2)≤2^W)
    (age : 512≤u) (hu : e+40≤u) (half : low=u^10/2) (depth : k+low≤u^10+2*u^6)
    (degree : d≤u) (slot : offsets*cells*3≤u^e) (trace : TraceBitHeader.seedTraceWork low stride cells
      B.cursorCopies (k+low)≤2^low*u^e) (level : B.levels+1≤u) (score : B.costFactors.sum≤u)
    (energy : 4*Real.sqrt B.blockError≤(u:ℝ)) (growth : Real.sqrt B.stageGrowth≤(u:ℝ))
    (peak : B.peakBase≤u) (unit : 0<tariff) (rate : tariff≤u^e)
    (saving : 146+2*e+26+(TraceVolume.cm+2)≤Aexp) (fuel : 2^(k+low)≤2*FoldTrace.hFuel u Aexp)
    (chunks : 0<shape.chunks) (chunk : shape.bits=2^(u^10-u^4))
    (timetable : 2^(u^6)=4*((ra).groups*clock.evaluateTicks)) (room : RootArchive.PublishRoom ra W)
    (numeric : RootLimits («W»:=W) («P»:=(R).plan) (bits:=bitCount) (c:=clock) («A»:=abi)
      (span:=2^low) (p:=pins) (H:=H) (J:=J) (fit:=fit) ra buckets terminal t
      ((buckets).cellInput («P»:=(R).plan) (bits:=bitCount) (c:=clock) («A»:=abi)
        (lanes:=2^k) (span:=2^low) (p:=pins) (H:=H) (J:=J) (w:=W) (fit:=fit)
        terminal t oa pairFit net lib hidden cellCap lut))
    {mid out : Memory W} (s : Selection («W»:=W) R C O (A).seedData start pay nd ra rs budget mid)
    (atTerminal : s.history=terminal.1) (stored : (R).ArchiveRowsStored (ra).nodeBank (natural out) s.history C O s.path)
    (team : ℕ) (memory : RootMemory («W»:=W) (c:=clock) («A»:=abi) ra t oa na oc nc rs out team) :
    let ns:=RootArchive.nodesOfRun («W»:=W) ra R s.history C O s.path out stored s.zero s.first s.card start pay
    RootInputs («W»:=W) («P»:=(R).plan) (bits:=bitCount) (c:=clock) («A»:=abi)
      (span:=2^low) (p:=pins) (H:=H) (J:=J) (fit:=fit) ra buckets terminal t oa na oc nc
      ((buckets).cellInput («P»:=(R).plan) (bits:=bitCount) (c:=clock) («A»:=abi)
        (lanes:=2^k) (span:=2^low) (p:=pins) (H:=H) (J:=J) (w:=W) (fit:=fit)
        terminal t oa pairFit net lib hidden cellCap lut) ns teamSlots rs out team := by
  intro ns
  have pinner : 0<u := by omega
  have vs : u^6≤u^10 := Nat.pow_le_pow_right pinner (by decide)
  have axes : k≤u^11 := by
    have big : 3*u^10≤u*u^10 := Nat.mul_le_mul_right _ (by omega)
    rw [show u^11=u*u^10 by ring];omega
  have sched : RootArchive.ScheduleFacts ra W teamSlots ns.work ns.pairs (ra).ids :=
    RootArchive.cursor_schedule_facts B hk ra s.history O s.path out stored s.zero s.first s.card shape
      clock.evaluateTicks age hu half.le axes depth degree slot trace level score energy growth peak unit rate
      saving fuel cover chunks chunk rfl rfl rfl timetable
  refine { toRootLimits:=numeric,toRootMemory:=memory,geometry:=room,schedule:=sched,home:=?_ }
  intro i
  have home:=Parameters.cursorBuckets_home B u rem low stride cells off tariff shape hk clock positive total cover
    s.history s.path out stored s.zero s.first s.card s.numbered numeric.ng room.lanes numeric.groupFits sched i
  exact home.trans (congrArg (fun j=>(buckets).group j ((R).plan.destination j ((buckets).site i))) atTerminal)


end
end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.TickPhysicalABI
open PhysicalStage NavigationDirectory NodePublication TickPhaseModel TickChronology TickAuxiliary ApproximateImage
open RAM.TickActiveROM RAM.TickBitRelation RAM.HistoryFactors RAM.Contraction RAM.BitLayout
open scoped Classical Fin.CommRing
noncomputable section

variable {F : Type} [Field F] [Fintype F] (B : Block F)
variable {u rem low stride cells off tariff e Aexp : ℕ} (shape : PhysicalPinsExpr.Shape)
local notation "pa" => Parameters.cursor B u rem low stride cells shape off tariff
local notation "W" => (16*u^10)
local notation "n" => (u^8)
local notation "d" => 2^B.exponent 0
local notation "P" => B.repeat n
local notation "k" => (P).charge+rem
local notation "offsets" => 1+((k+low)+(k+low))
local notation "A" => (pa).archive d W
variable (hk : 2 ≤ (B.repeat (u^8)).charge + rem)
local notation "X" => B.cursorState hk low offsets cells
local notation "R" => (P).run rem X
local notation "visits" => (P).directory rem (Fintype.card (X).Base)
local notation "edges" => (P).finalEdges rem (Fintype.card (X).Base)
local notation "ss" => (P).directory rem (pa).axes
local notation "nd" => (pa).nodeArchive A ss W
local notation "ra" => (pa).rootArchive A nd ss W
local notation "rs" => nodeLayers (A).K ss (A).cursor (A).seedLayer
local notation "O" => (A).cursorSeedSites B hk low offsets cells rfl rfl
local notation "C" => B.charges n rem X
local notation "start" => B.seedWork hk low offsets cells (2*shape.halfBits) B.cursorCopies (k+low) stride cells
local notation "pay" => B.clippedPairs hk low offsets cells (2*shape.halfBits)
local notation "piece" => (2^(u^10-u^4):ℕ)
local notation "budget" => u*(piece+1)
local notation "bitCount" => (R).readTerminal (fun z=>z.widthSum)
local notation "lib" => Parameters.gridWords B u
local notation "suffix" => nodeTape (nd).banks (nd).headerBase rs++(List.ofFn (fun j : Fin 22=>(ra).word j)++stageTape rs)
local notation "work" => (A).bootTime visits edges W+(A).seedTime+6+((A).loopTime (u:=u) B n rem X+Archive.terminalTime ((A).terminal visits edges W))

variable (clock : Clock) (positive : 0<clock.groups) (total : clock.chunks=2*shape.chunks)
    (cover : 2*shape.halfBits ≤ 2^(((B.repeat (u^8)).charge + rem) + low))
local notation "buckets" => Parameters.cursorBuckets B u rem low stride cells off tariff shape hk clock positive total cover
variable {teams : ℕ} (team t : ℕ) (D : Fin shape.advice→Bool) (par : Fin shape.parameterBits→Bool)
    (oa na oc nc : Aux shape.bits)
local notation "abi" => TickPhysicalABI.mounted u shape.bits teams (shape.bits/2) shape.advice shape.teamBits shape.timeBits shape.parameterBits
local notation "teamSlots" => clock.evaluateTicks*2^(u^3)
local notation "pin" => fields D (digits team shape.teamBits) (digits t shape.timeBits) par oa na oc nc
local notation "entry" => TickNavigationEntry.input abi clock team t (TickMountedPins.memory (w:=W) pin)
local notation "rawBit" => entryHistory (clock.phase t) oa na

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 14000 in
/-- A successfully decoded mounted tick runs the actual navigator and produces the same
prepared input consumed by the selected history procedure, within the full tick clock. -/
theorem accepted_navigation {pins H J : ℕ} {fit : Fits (TickWeightedBank.shape F pins H J) W}
    (field : FieldCode F W) (age : 384000≤u) (hu : e+40≤u) (half : low=u^10/2)
    (depth : k+low≤u^10+2*u^6) (fixed : directoryCap B≤u) (fixedTime : 10*nodeWriterBudget B≤u)
    (alphabet : B.alphabetCap≤u) (levels : B.levels+1≤u) (score : B.costFactors.sum≤u)
    (allocation : B.allocations.sum≤u) (moveWords : fixedMoveWords B≤u)
    (tables : HistoryStageBody.Physical.staticSize B+HistoryStageBody.Physical.gridSize B≤u)
    (coefficient : B.nativeCoefficient B.alphabetCap≤u)
    (growth : B.widthBase≤u) (factor : B.repeatFactor≤u) (peak : B.peakBase≤u)
    (energy : 4*Real.sqrt B.blockError≤(u:ℝ)) (stageGrowth : Real.sqrt B.stageGrowth≤(u:ℝ))
    (unit : 0<tariff) (rate : tariff≤u^e) (slot : offsets*cells*3≤u^e)
    (trace : TraceBitHeader.seedTraceWork low stride cells B.cursorCopies (k+low)≤2^low*u^e)
    (saving : 146+2*e+26+(TraceVolume.cm+2)≤Aexp) (fuel : 2^(k+low)≤2*FoldTrace.hFuel u Aexp)
    (chunks : 0<shape.chunks) (chunk : shape.bits=piece) (groups : 1024*(2*shape.chunks)≤piece)
    (timetable : 2^(u^6)=4*((ra).groups*clock.evaluateTicks)) (ng : clock.groups=1024*(2*shape.chunks))
    (last : clock.last+1=2^(u^6)) (tick : t<2^(u^6))
    (bounds : WordBounds abi fit) (pinsLow : 2+pinCount shape.advice shape.teamBits shape.timeBits
      shape.parameterBits shape.bits≤(abi).control)
    (parameterFit : off+W*(lib++(pa).staticWords B n rem W).length ≤ shape.parameterBits)
    (src : (A).SeedSources visits edges lib suffix rawBit entry) (window : (A).RawWindow visits rawBit entry)
    (terminal : HistoryContraction.Plan.Terminal (R).plan bitCount) (net : BitNetwork F pins) (book : Library net)
    (hidden : net.internal≤H) (cellCap : net.cells+(H-net.internal)≤J) (lut : (abi).lut+8*(book.count+2)≤2^W)
    (decoded : let bound:=B.cursor_repeat_word hu (le_trans (le_of_eq half) (Nat.div_le_self (u^10) 2)) growth factor slot hk
      let Q:=B.recordTable B.alphabetCap W n rem X le_rfl bound
      (R).plan.decodeShared Q.codes bitCount (A).pairCapacity (List.ofFn (fun j : Fin (A).pairCapacity=>rawBit j.val))=
        some terminal) :
    let bound:=B.cursor_repeat_word hu (le_trans (le_of_eq half) (Nat.div_le_self (u^10) 2)) growth factor slot hk
    let Q:=B.recordTable B.alphabetCap W n rem X le_rfl bound
    let origin : Memory W := (A).startedMemory visits edges lib rawBit entry n
    let closed : Memory W → Prop := (A).Closed B n rem X rawBit Q.records origin
    let raw : List Bool := List.ofFn (fun j : Fin (A).pairCapacity=>rawBit j.val)
    let accepted : Option (HistoryContraction.Plan.Terminal (R).plan bitCount) := (R).plan.decodeShared Q.codes bitCount (A).pairCapacity raw
    let machine : Procedure W := (pa).machine («W»:=W) B n rem
    let time : ℕ := work+(nodeTime W (rs).length budget+(ra).publishCost W)
    ∃ pairFit : 1+(abi).capacity+2*(buckets).length terminal (clock.group t)≤(abi).bits,
      let cell : CellInput abi clock fit := (buckets).cellInput («P»:=(R).plan) (bits:=bitCount) («A»:=abi) (c:=clock)
        (lanes:=2^k) (span:=2^low) (p:=pins) (H:=H) (J:=J) (w:=W) (fit:=fit) terminal t oa pairFit net book hidden cellCap lut
      let next : Memory W → Prop := CursorSlot («W»:=W) («d»:=d) (l:=k) («X»:=X) («P»:=(R).plan) (bits:=bitCount)
        («A»:=abi) (c:=clock) (span:=2^low) (p:=pins) (H:=H) (J:=J) (fit:=fit) R C O (A).seedData start pay nd ra rs budget buckets terminal t oa na oc nc
        pairFit net book hidden cellCap lut closed (·=terminal.1) teamSlots team
          (fun _ s=>s.AtProgram (A).K (finish (A).K ((P).directory rem (pa).axes) (A).cursor) (fun Pins=>(P).assembly (Pins:=Pins) rem X) B.publicTemplate)
      TickStageSpec.Admission (w:=W) («n»:=machine.labels) (nr:=machine.registers) («k»:=machine.slots)
        field machine.block machine.publicData (·=entry) (fun _=>accepted.isSome)
        (fun _ out=>NavOutput (B:=abi) (clock:=clock) (fit:=fit) cell (clock.phase t) oa na oc nc next out) time ∧
        time≤TickTotalBudget.replayBound u 20 104000 := by
  intro bound Q origin closed raw accepted machine time
  have deg : d≤u := by unfold directoryCap at fixed;omega
  have pos : 0<u := by omega
  have us : u≤u^10 := Nat.le_self_pow (by decide) _
  have vs : u^6≤u^10 := Nat.pow_le_pow_right pos (by decide)
  have axes : k≤u^11 := by
    have mul := Nat.mul_le_mul_right (u^10) (show 3≤u by omega)
    rw [show u^11=u*u^10 by ring];omega
  have pairLim : 2*shape.halfBits≤2^(3*u^10) := cover.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have enough : (ra).groups=clock.groups := ng.symm
  have pairFit:=Parameters.cursor_pairSpace B (u:=u) (rem:=rem) (low:=low)
    (stride:=stride) (cells:=cells) (tableOffset:=off) (tariff:=tariff) (e:=e) (Aexp:=Aexp)
    shape hk clock positive total cover
    (by omega) hu half.le axes depth deg slot trace levels score energy stageGrowth peak unit rate saving fuel chunks
    chunk timetable enough terminal (clock.group t)
  refine ⟨pairFit,?_⟩
  intro cell next
  obtain ⟨nodeRoom,nodeTicks⟩:=cursor_run_budget B shape (by omega) fixed fixedTime levels allocation half depth pairLim
  obtain ⟨rootSpace,rootTicks⟩:=RootArchive.cursor_root_budget B shape (by omega) levels allocation half depth groups chunk.le pairLim
  have lanes:=program_lanes_le_final P pa rem d W rfl (by change 0<k;omega)
  have rawLow : 2+shape.advice+shape.teamBits+shape.timeBits+shape.parameterBits≤TickWorkspace.stride u := by
    exact raw_prefix_below_stride pinsLow
  have physical:=rootSpace lanes (RootArchive.cursor_raw_room B u rem low stride cells shape off tariff d parameterFit rawLow)
  have card : Fintype.card (X).Base=(pa).axes := Fintype.card_fin k
  have limits : (A).Limits u ((A).control:Word W) visits edges (A).pairCapacity := by
    rw [card];exact Parameters.cursor_limits B shape (by omega) levels allocation score alphabet half depth chunk _
  have nums:=RootABI.cursor_limits B shape hk clock positive total cover teams (shape.bits/2) (by omega) depth
    chunk.le ng last bounds terminal t tick oa pairFit net book hidden cellCap lut
  have obtainMemory (out : Memory W) (ok : closed out) :=
    cursor_closed_root_memory B shape hk clock team t D par oa na oc nc (by omega : 40≤u) deg half depth alphabet
      levels score nodeRoom physical limits out src Q.records ok parameterFit pinsLow
  constructor
  · apply cursor_selected_tick B shape hk field hu half depth deg slot alphabet levels score allocation moveWords
      growth factor chunk rawBit lib suffix entry src window buckets terminal t oa na oc nc pairFit net book hidden
      cellCap lut teamSlots team fixed fixedTime peak rate trace pairLim
    refine ⟨decoded,fun m ok=>(obtainMemory m ok).1,?_⟩
    intro mid valid s same profile out eq charged stored
    have mem : RootMemory (c:=clock) («A»:=abi) ra t oa na oc nc rs out team := by
      rw [eq]
      exact (obtainMemory mid valid).2 s.layout (program ((R).archiveList s.history C O s.path (A).seedData))
    exact cursor_root_inputs B shape hk clock positive total cover teams (shape.bits/2) terminal t oa na oc nc
      pairFit net book hidden cellCap lut (by omega) hu half depth deg slot trace levels score energy stageGrowth
      peak unit rate saving fuel chunks chunk timetable physical nums s same stored team mem
  · have active:=Parameters.cursor_active_time B (stride:=stride) (cells:=cells) (tableOffset:=off) (tariff:=tariff)
      shape hk age half depth deg alphabet levels score tables coefficient chunk
    have ageCost : u*piece≤u^20*piece := Nat.mul_le_mul_right _ (Nat.le_self_pow (by decide) _)
    change work+(nodeTime W (rs).length budget+(ra).publishCost W)≤104000*u^20*piece
    change nodeTime W (rs).length budget≤3000*u^20*piece at nodeTicks
    change (ra).publishCost W≤100000*u^20*piece at rootTicks
    nlinarith only [active,nodeTicks,rootTicks,ageCost]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 12000 in
/-- A malformed raw string at exactly the same mounted ABI halts before the node and
root passes and costs at most one linear-in-age scan of the chunk. -/
theorem rejected_navigation (field : FieldCode F W) (age : 384000≤u) (hu : e+40≤u)
    (half : low=u^10/2) (depth : k+low≤u^10+2*u^6) (degree : d≤u)
    (alphabet : B.alphabetCap≤u) (levels : B.levels+1≤u) (score : B.costFactors.sum≤u)
    (allocation : B.allocations.sum≤u) (moveWords : fixedMoveWords B≤u)
    (tables : HistoryStageBody.Physical.staticSize B+HistoryStageBody.Physical.gridSize B≤u)
    (coefficient : B.nativeCoefficient B.alphabetCap≤u) (growth : B.widthBase≤u)
    (factor : B.repeatFactor≤u) (slot : offsets*cells*3≤u^e) (chunk : shape.bits=piece)
    (src : (A).SeedSources visits edges lib suffix rawBit entry) (window : (A).RawWindow visits rawBit entry)
    (decoded : let bound:=B.cursor_repeat_word hu (le_trans (le_of_eq half) (Nat.div_le_self (u^10) 2)) growth factor slot hk
      let Q:=B.recordTable B.alphabetCap W n rem X le_rfl bound
      (R).plan.decodeShared Q.codes bitCount (A).pairCapacity
        (List.ofFn (fun j : Fin (A).pairCapacity=>rawBit j.val))=none) :
    let machine : Procedure W := (pa).machine («W»:=W) B n rem
    TickStageSpec.Admission (w:=W) («n»:=machine.labels) (nr:=machine.registers) («k»:=machine.slots)
        field machine.block machine.publicData (·=entry) (fun _=>False)
      (fun _ _=>False) work ∧ work≤u*piece := by
  intro machine
  exact ⟨cursor_machine_reject B shape hk field hu half depth degree slot alphabet levels score allocation
    moveWords growth factor chunk rawBit lib suffix entry src window decoded,
    Parameters.cursor_active_time B shape hk age half depth degree alphabet levels score tables coefficient chunk⟩


section
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option showPartialSyntaxErrors true
variable (keepProgram : Bool)

private def mountedBudget {F : Type} [Field F] {width : ℕ} (field : FieldCode F width)
    (machine : Procedure width) (input : Memory width) (admitted : Prop)
    (outputs : Memory width → Prop) (ticks limit : ℕ) : Prop :=
  TickStageSpec.Admission (w:=width) («n»:=machine.labels) (nr:=machine.registers) («k»:=machine.slots)
    field machine.block machine.publicData (·=input) (fun _ => admitted)
    (fun _ out => outputs out) ticks ∧ ticks ≤ limit

private def mountedProfile (keepProgram : Bool) (directory program : Prop) : Prop :=
  if keepProgram then program else directory

private theorem mountedProfile_of_program (keepProgram : Bool) {directory program : Prop}
    (weakens : program → directory) (h : program) : mountedProfile keepProgram directory program := by
  cases keepProgram
  · exact weakens h
  · exact h

def mountedRegisterOutcome {pins H J : ℕ} {fit : Fits (TickWeightedBank.shape F pins H J) W}
    (field : FieldCode F W) (decoded : Option (HistoryContraction.Plan.Terminal (R).plan bitCount))
    (closed : Memory W → Prop) : Prop :=
    let machine : Procedure W := (pa).machine («W»:=W) B n rem
    let navWork : ℕ := work
    let time : ℕ := navWork+(nodeTime W (rs).length budget+(ra).publishCost W)
    (∀ terminal : HistoryContraction.Plan.Terminal (R).plan bitCount, decoded=some terminal → ∀ (net : BitNetwork F pins) (book : Library net)
      (hidden : net.internal≤H) (cellCap : net.cells+(H-net.internal)≤J) (lut : (abi).lut+8*(book.count+2)≤2^W),
      ∃ pairFit : 1+(abi).capacity+2*(buckets).length terminal (clock.group t)≤(abi).bits,
      let cell : CellInput abi clock fit := (buckets).cellInput («P»:=(R).plan) (bits:=bitCount)
        («A»:=abi) (c:=clock) (lanes:=2^k) (span:=2^low) (p:=pins) (H:=H) (J:=J) (w:=W)
        (fit:=fit) terminal t oa pairFit net book hidden cellCap lut
      let next : Memory W → Prop := CursorSlot («W»:=W) («d»:=d) (l:=k) («X»:=X) («P»:=(R).plan)
        (bits:=bitCount) («A»:=abi) (c:=clock) (span:=2^low) (p:=pins) (H:=H) (J:=J) (fit:=fit)
        R C O (A).seedData start pay nd ra rs budget buckets terminal t oa na oc nc
        pairFit net book hidden cellCap lut closed (·=terminal.1) teamSlots team
          (fun _ s => mountedProfile keepProgram (s.AtDirectory (A).K (finish (A).K ss (A).cursor))
            (s.AtProgram (A).K (finish (A).K ss (A).cursor)
              (fun Pins => (P).assembly (Pins:=Pins) rem X) B.publicTemplate))
      mountedBudget field machine entry True
        (NavOutput (B:=abi) (clock:=clock) (fit:=fit) cell (clock.phase t) oa na oc nc next)
        time (TickTotalBudget.replayBound u 20 104000)) ∧
    (decoded=none → mountedBudget field machine entry False (fun _ => False)
      navWork (TickTotalBudget.replayBound u 20 104000))


/-- Every physical group register is interpreted through the same record table and mounted entry. -/
def mountedRegisterFamily {pins H J : ℕ} {fit : Fits (TickWeightedBank.shape F pins H J) W}
    (field : FieldCode F W) (bound : B.repeatFactor*(((X).maxWidth+1)*B.widthBase^n)<2^W) : Prop :=
    let Q:=B.recordTable B.alphabetCap W n rem X le_rfl bound
    ∀ reg : GroupRegister (R).plan Q.codes bitCount shape.bits, reg.capacity=shape.bits/2 →
    let decoded : Option (HistoryContraction.Plan.Terminal (R).plan bitCount) :=
      TickAuxiliary.decode (a:=shape.bits) (R).plan Q.codes bitCount reg.base (if clock.phase t=.opening then na else oa)
    let closed : Memory W → Prop := (A).Closed (u:=u) B n rem X rawBit Q.records ((A).startedMemory («W»:=W) visits edges lib rawBit entry n)
    NativeNavigation.mountedRegisterOutcome (keepProgram:=keepProgram) (B:=B) (shape:=shape) (hk:=hk)
      (u:=u) (rem:=rem) (low:=low) (stride:=stride) (cells:=cells) (tariff:=tariff)
      (off:=off) (teams:=teams)
      (clock:=clock) (positive:=positive) (total:=total) (cover:=cover)
      (team:=team) (t:=t) (D:=D) (par:=par) (oa:=oa) (na:=na) (oc:=oc) (nc:=nc)
      (pins:=pins) (H:=H) (J:=J) (fit:=fit) field decoded closed

end

end
end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.TickPhysicalABI
open PhysicalStage NavigationDirectory NodePublication TickPhaseModel TickChronology TickAuxiliary ApproximateImage
open RAM.TickActiveROM RAM.TickBitRelation RAM.HistoryFactors RAM.Contraction RAM.BitLayout
open scoped Classical Fin.CommRing
noncomputable section

variable (keepProgram : Bool)
variable {F : Type} [Field F] [Fintype F] (B : Block F)
variable {u rem low stride cells tariff e Aexp nt ns inside period last paramBase templateBase : ℕ}
variable (I : PhysicalPrelude.Image F (16*u^10))
private def mountedShape (nt ns inside period last paramBase templateBase : ℕ) : PhysicalPinsExpr.Shape :=
  ⟨I.advice,nt,ns,I.parameters,2^(u^10-u^4),inside,2^(u^3),period,last,paramBase,templateBase⟩
local notation "shape" => mountedShape (u:=u) I nt ns inside period last paramBase templateBase
local notation "pa" => Parameters.cursor B u rem low stride cells shape 0 tariff
local notation "W" => (16*u^10)
local notation "n" => (u^8)
local notation "d" => 2^B.exponent 0
local notation "P" => B.repeat n
local notation "k" => (P).charge+rem
local notation "offsets" => 1+((k+low)+(k+low))
local notation "A" => (pa).archive d W
variable (hk : 2 ≤ (B.repeat (u^8)).charge + rem)
local notation "X" => B.cursorState hk low offsets cells
local notation "R" => (P).run rem X
local notation "visits" => (P).directory rem (Fintype.card (X).Base)
local notation "edges" => (P).finalEdges rem (Fintype.card (X).Base)
local notation "ss" => (P).directory rem (pa).axes
local notation "nd" => (pa).nodeArchive A ss W
local notation "ra" => (pa).rootArchive A nd ss W
local notation "rs" => nodeLayers (A).K ss (A).cursor (A).seedLayer
local notation "O" => (A).cursorSeedSites B hk low offsets cells rfl rfl
local notation "C" => B.charges n rem X
local notation "start" => B.seedWork hk low offsets cells (2*(shape).halfBits) B.cursorCopies (k+low) stride cells
local notation "pay" => B.clippedPairs hk low offsets cells (2*(shape).halfBits)
local notation "piece" => (2^(u^10-u^4):ℕ)
local notation "budget" => u*(piece+1)
local notation "bitCount" => (R).readTerminal (fun z=>z.widthSum)
local notation "lib" => Parameters.gridWords B u
local notation "suffix" => nodeTape (nd).banks (nd).headerBase rs++(List.ofFn (fun j : Fin 22=>(ra).word j)++stageTape rs)

variable (clock : Clock) (positive : 0<clock.groups) (total : clock.chunks=2*(period*(inside+1)))
    (cover : 2*((period*(inside+1))*2^(u^10-u^4))≤2^(((B.repeat (u^8)).charge+rem)+low))
local notation "buckets" => Parameters.cursorBuckets B u rem low stride cells 0 tariff shape hk clock positive total cover
local notation "teams" => (2^(u^3):ℕ)
variable (team t : ℕ) (D : Fin I.advice→Bool) (par : Fin I.parameters→Bool)
    (oa na oc nc : Fin (2^(u^10-u^4))→Bool)
local notation "abi" => TickPhysicalABI.mounted u piece teams (piece/2) I.advice nt ns I.parameters
local notation "teamSlots" => clock.evaluateTicks*2^(u^3)
local notation "pin" => fields D (digits team nt) (digits t ns) par oa na oc nc
local notation "entry" => TickNavigationEntry.input abi clock team t (TickMountedPins.memory (w:=W) pin)
local notation "rawBit" => entryHistory (clock.phase t) oa na


set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option showPartialSyntaxErrors true

/-- On the actual public input, both outcomes use one mounted navigator. Accepted
rows expose their chronological selected-state predicate. Every rejected input has
zero mass under the very same word, register, and timing layout. -/
theorem mountedNavigationWith {pins H J : ℕ} {fit : Fits (TickWeightedBank.shape F pins H J) W}
    (field : FieldCode F W) (age : 384000≤u) (hu : e+40≤u) (half : low=u^10/2)
    (depth : k+low≤u^10+2*u^6) (fixed : directoryCap B≤u) (fixedTime : 10*nodeWriterBudget B≤u)
    (alphabet : B.alphabetCap≤u) (levels : B.levels+1≤u) (score : B.costFactors.sum≤u)
    (allocation : B.allocations.sum≤u) (moveWords : fixedMoveWords B≤u)
    (tables : HistoryStageBody.Physical.staticSize B+HistoryStageBody.Physical.gridSize B≤u)
    (coefficient : B.nativeCoefficient B.alphabetCap≤u)
    (growth : B.widthBase≤u) (factor : B.repeatFactor≤u) (peak : B.peakBase≤u)
    (energy : 4*Real.sqrt B.blockError≤(u:ℝ)) (stageGrowth : Real.sqrt B.stageGrowth≤(u:ℝ))
    (unit : 0<tariff) (rate : tariff≤u^e) (slot : offsets*cells*3≤u^e)
    (trace : TraceBitHeader.seedTraceWork low stride cells B.cursorCopies (k+low)≤2^low*u^e)
    (saving : 146+2*e+26+(TraceVolume.cm+2)≤Aexp) (fuel : 2^(k+low)≤2*FoldTrace.hFuel u Aexp)
    (chunks : 0<(shape).chunks) (groups : 1024*(2*(shape).chunks)≤piece)
    (timetable : 2^(u^6)=4*((ra).groups*clock.evaluateTicks)) (ng : clock.groups=1024*(2*(shape).chunks))
    (last_ : clock.last+1=2^(u^6)) (tick : t<2^(u^6))
    (bounds : WordBounds abi fit) (adv : I.advice=2^(u^3)) («meta» : 2+nt+ns+I.parameters≤u^e)
    (extraWords : List ℕ) (tmp : ℕ) (es : List (EffectStream.Record W))
    (allFit : W*((((lib++(pa).staticWords B n rem W)++extraWords).length)+2*es.length)+
      W*FixedTraceImage.count I.G≤I.parameters)
    (mounted : let ws:=(lib++(pa).staticWords B n rem W)++extraWords
      TraceMountedParameters.parameters I 0 (ws.length+2*es.length)
        (TraceMountedParameters.seedWords ws.length tmp (fun i=>(ws[i]?.getD 0 : Word W)) es)
        (fun _=>false)=par) :
    NativeNavigation.mountedRegisterFamily (keepProgram:=keepProgram) (B:=B) («shape»:=shape) (hk:=hk)
      (u:=u) (rem:=rem) (low:=low) (stride:=stride) (cells:=cells) (tariff:=tariff)
      (off:=0) («teams»:=teams)
      (clock:=clock) (positive:=positive) (total:=total) (cover:=cover)
      (team:=team) (t:=t) (D:=D) (par:=par) (oa:=oa) (na:=na) (oc:=oc) (nc:=nc)
      (pins:=pins) (H:=H) (J:=J) (fit:=fit) field
      (B.cursor_repeat_word (u:=u) (rem:=rem) (low:=low) (off:=offsets) (slots:=cells) (e:=e)
        hu (le_trans (le_of_eq half) (Nat.div_le_self (u^10) 2)) growth factor slot hk) := by
  unfold mountedRegisterFamily
  intro Q reg capacity decoded closed
  have degree : d≤u := calc
    d ≤ 2*d := Nat.le_mul_of_pos_left _ (by decide : 0<2)
    _ ≤ directoryCap B := Nat.le_add_right _ _
    _ ≤ u := fixed
  have m:=Parameters.mounted_cursor_source (inside:=inside) (period:=period) (last:=last)
    (paramBase:=paramBase) (templateBase:=templateBase) (stride:=stride) (cells:=cells) (tariff:=tariff)
    («teams»:=teams) B I D par clock team t oa na oc nc extraWords tmp es
    ((by decide : 40≤384000).trans age) half depth hk
    degree levels allocation score alphabet adv ((Nat.le_add_right e 40).trans hu) «meta» allFit mounted
  have card : Fintype.card (X).Base=(pa).axes:=Fintype.card_fin _
  have sources : (A).SeedSources visits edges lib suffix rawBit entry:=by rw [card];exact m.1
  have window : (A).RawWindow visits rawBit entry:=by rw [card];exact m.2.1
  have eqn : (R).plan.decodeShared Q.codes bitCount (A).pairCapacity
      (List.ofFn (fun j : Fin (A).pairCapacity=>rawBit j.val))=decoded := by
    have q:=entryHistory_decode (R).plan Q.codes bitCount reg (clock.phase t) oa na
    rw [capacity] at q
    exact q
  constructor
  · intro terminal valid net book hidden cellsCap lut
    have h:=eqn.trans valid
    obtain ⟨pairFit,accept,dur⟩:=accepted_navigation (off:=0) («teams»:=teams) (pins:=pins)
      (H:=H) (J:=J) (fit:=fit) B shape hk clock positive total cover
      team t D par oa na oc nc field age hu half depth fixed fixedTime alphabet levels score allocation
      moveWords tables coefficient growth factor peak energy stageGrowth unit rate slot trace saving fuel
      chunks rfl groups timetable ng last_ tick bounds m.2.2.1
      (by simpa only [Nat.zero_add,mountedShape] using m.2.2.2)
      sources window terminal net book hidden cellsCap lut h
    refine ⟨pairFit,?_⟩
    intro cell next
    refine ⟨TickStageSpec.Admission.mono accept (fun _ prior=>prior) ?_ ?_ le_rfl,dur⟩
    · intro mem _
      change True ↔ ((R).plan.decodeShared Q.codes bitCount (A).pairCapacity
        (List.ofFn (fun j : Fin (A).pairCapacity=>rawBit j.val))).isSome = true
      exact ⟨fun _=>congrArg Option.isSome h,fun _=>True.intro⟩
    · intro mem out _ _ nav
      refine {nav with evalInputs:=?_}
      intro evaluating
      obtain ⟨mid,hclosed,s,selected,profile,tail⟩ := nav.evalInputs evaluating
      exact ⟨mid,hclosed,s,selected,mountedProfile_of_program keepProgram (fun _ => profile.1) profile,tail⟩
  · intro malformed
    obtain ⟨bad,dur⟩:=rejected_navigation (off:=0) («teams»:=teams) B shape hk clock team t D par oa na oc nc field age hu
      half depth degree alphabet levels score allocation moveWords tables coefficient growth factor slot rfl
      sources window (eqn.trans malformed)
    have ageBound : u≤104000*u^20 := (Nat.le_self_pow (by decide : 20≠0) u).trans
      (Nat.le_mul_of_pos_left (u^20) (by decide : 0<104000))
    exact ⟨bad,dur.trans (Nat.mul_le_mul_right piece ageBound)⟩


/-- Directory and timing conclusions for both outcomes of the mounted navigator. -/
abbrev mounted_navigation := @NativeNavigation.mountedNavigationWith false

/-- In the selected branch the same navigator also retains the ordered physical program visits. -/
abbrev mounted_program_navigation := @NativeNavigation.mountedNavigationWith true

end
end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

end OAI
