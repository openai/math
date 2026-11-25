import OAI.Hierarchy.DescentNamedBranchMachine
import OAI.Hierarchy.DescentRegisteredRangeRoom
import OAI.Hierarchy.DescentIssuedPrefixPitch
import OAI.Hierarchy.DescentIssuedLastReset
import OAI.Hierarchy.DescentCalendarRangeReturn

namespace OAI
/-! # The physical operand geometry on every reached cut of the named register calendar -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline

open Computability.VPVNP.BurstRAM PrivateRAM DescentDatedAddressBook
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)
local notation "steps" => issued (w:=w) traces b
local notation "cursor" => calendar (w:=w) traces b initial
variable (fixed : ∀i (a z : RunTrace.Events traces i) x y,
  issued (w:=w) traces b i a (calendar (w:=w) traces b initial i) x→issued (w:=w) traces b i z (calendar (w:=w) traces b initial i) y→x=y)
variable (start : Rooms G S b k w 0 initial)
variable (installed : ∀i (e : RunTrace.Events traces i),Rooms G S b k w i (calendar (w:=w) traces b initial i)→
  ∃move : Move w,issued (w:=w) traces b i e (calendar (w:=w) traces b initial i) move ∧ move.next.floor<2^w ∧
    (e.2.isReset=true→8*b.receiverWidth G S k i (calendar (w:=w) traces b initial i).ports ≤ b.payload))

variable (c : C)
local notation "t" => traces c

omit [Fintype P] in
include fixed start installed in
private theorem operandGeometryOnTrace
    (originSize : Fintype.card (t).first.V ≤ initial.ports.operandHosts)
    (originK : initial.ports.venue.k = k)
    (numberOrdinary :
      ∀ {U : MarkedWorld F d P bits} {age z D z' D' : ℕ} {rate : ℝ}
        {src : Reached U G q ε S k age z D wire hist} {nneg : 0 ≤ ε}
        {T : StageInput U G rate ε} {ballot : (T.result nneg).Choice}
        {norm : Normalize ((T.result nneg).state ballot)}
        {dst : Reached norm.result G q ε S k (age+1) z' D' wire hist}
        (ticket : OrdinaryLink src nneg T ballot norm dst)
        (prev : Path (t).first src) (rest : Path dst (t).last),
        (prev.ordinary ticket).append rest = (t).path →
        ∀ at_ : Position, Fintype.card dst.V ≤
          (DatePorts.ordinaryPorts at_.ports ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit
            b.payload (b.seats age) at_.floor b.ordinary).operandHosts)
    {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (prefix_ : Path (t).first r) (suffix_ : Path r (t).last)
    (joined : prefix_.append suffix_=(t).path) :
    Fintype.card r.V ≤ (cursor i).ports.operandHosts ∧ (cursor i).ports.venue.k = k := by
  induction prefix_ with
  | here => exact ⟨originSize,originK⟩
  | @ordinary _ age _ _ _ _ src prev _ he T ballot norm dst ticket ih =>
    let e : (t).path.Event age := .ordinary prev ticket suffix_ joined
    have mid := (Path.append_cut_assoc prev (Path.here.ordinary ticket) suffix_).symm.trans joined
    have old := rooms_prefix traces b initial fixed start installed c prev _ mid
    obtain ⟨move,posted,_,_⟩ := installed age ⟨c,e⟩ old
    have step := (returned traces b initial age ⟨c,e⟩ move posted
      (fun a y hy => fixed age a ⟨c,e⟩ y move hy posted)).2
    obtain ⟨pos,space,rfl⟩ := posted
    rw [step]
    refine ⟨numberOrdinary ticket prev suffix_ joined _,?_⟩
    rfl
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed ih =>
    let e : (t).path.Event age := .reset prev closed suffix_ joined
    have mid := (Path.append_cut_assoc prev (Path.here.reset closed) suffix_).symm.trans joined
    have old := rooms_prefix traces b initial fixed start installed c prev _ mid
    obtain ⟨move,posted,_,_⟩ := installed age ⟨c,e⟩ old
    have step := (returned traces b initial age ⟨c,e⟩ move posted
      (fun a y hy => fixed age a ⟨c,e⟩ y move hy posted)).2
    obtain ⟨cap,space,rfl⟩ := posted
    rw [step]
    exact ⟨closed.next.valid.host,(ih _ mid).2⟩
end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline


namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline

open Computability.VPVNP.BurstRAM PrivateRAM DescentDatedAddressBook
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)
local notation "steps" => issued (w:=w) traces b
local notation "cursor" => calendar (w:=w) traces b initial
variable (fixed : ∀i (a z : RunTrace.Events traces i) x y,
  issued (w:=w) traces b i a (calendar (w:=w) traces b initial i) x→issued (w:=w) traces b i z (calendar (w:=w) traces b initial i) y→x=y)
variable (start : Rooms G S b k w 0 initial)
variable (installed : ∀i (e : RunTrace.Events traces i),Rooms G S b k w i (calendar (w:=w) traces b initial i)→
  ∃move : Move w,issued (w:=w) traces b i e (calendar (w:=w) traces b initial i) move ∧ move.next.floor<2^w ∧
    (e.2.isReset=true→8*b.receiverWidth G S k i (calendar (w:=w) traces b initial i).ports ≤ b.payload))

variable (c : C)
local notation "t" => traces c

set_option quotPrecheck false
open DescentDatedPriorOperand

omit [Fintype P] in
private theorem venueKeyOnEvent
    (prefixKey : ∀{U : MarkedWorld F d P bits} {i z D : ℕ}
      {r : Reached U G q ε S k i z D wire hist} (pr : Path (t).first r) (sf : Path r (t).last),
      pr.append sf = (t).path → (cursor i).ports.venue.k = k)
    {i : ℕ} (e : (t).path.Event i) : (cursor i).ports.venue.k = k := by
  cases e with
  | ordinary before ticket after joined =>
    exact prefixKey before ((Path.here.ordinary ticket).append after)
      ((Path.append_cut_assoc before (Path.here.ordinary ticket) after).symm.trans joined)
  | reset before closed after joined =>
    exact prefixKey before ((Path.here.reset closed).append after)
      ((Path.append_cut_assoc before (Path.here.reset closed) after).symm.trans joined)

local notation "lastAge" => final - 1
local notation "old" => cursor lastAge
local notation "atReset" => PhysicalReset.scheduledAtPorts G S b.board k b.tail lastAge b.p b.f b.gain b.drift
  b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) (old).ports (old).floor
local notation "output" => (atReset).inner.successor
local notation "base" => (atReset).inner.rebased ((atReset).inner.stageStart ((old).ports.priorStart k (old).floor))

omit [Fintype P] in
include fixed start installed in
private theorem finalRegisteredFields {p : ℕ} (ending : Path.FinalReset p (t).path)
    (previousK : (old).ports.venue.k = k) :
    (cursor final).ports.archive = PriorResetArchive.reset output base ∧
      (cursor final).ports.rangeLayout = (output).rangeLayout ∧
      (cursor final).ports.operandBits = (output).nodeBits := by
  have address := rooms_on_event traces b initial fixed start installed c lastAge ending.event
  obtain ⟨mv, posted, _, _⟩ := installed lastAge ⟨c,ending.event⟩ address
  obtain ⟨cap, space, _, _, returnedPos⟩ := final_move traces b initial c ending fixed ⟨mv,posted⟩
  rw [returnedPos]
  refine ⟨rfl,?_,rfl⟩
  apply PhysicalReset.scheduled_range_layout
  exact previousK
end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentRetainedRangeDigits DescentDatedPriorOperand DescentDatedAddressBook
open DescentLocalArchiveOrder DescentKernelHistory Computability.VPVNP.BurstRAM ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule}
    {k wire hist w : ℕ} {W₀ W : MarkedWorld F d P bits} {i₀ z₀ D₀ j z D : ℕ}
    {start : Reached W₀ G q ε S k i₀ z₀ D₀ wire hist} {now : Reached W G q ε S k j z D wire hist}
    {p : ℕ} (hp : 0<p) (a : Archive W₀) (number : Local a.bit) (path : Path start now)
    (ports : ℕ→DatePorts) (memory : ℕ→Memory w)
    (room : ∀{U : MarkedWorld F d P bits} {i g C : ℕ} {r : Reached U G q ε S k i g C wire hist},
      ∀(prefix_ : Path start r) (wh : prefix_.whole p),
        (∃suffix_ : Path r now,prefix_.append suffix_=path) → RangeRoom (ports i) r (prefix_.archive p hp a wh).bit)
    (whole : path.whole p) (v : ResetOutput) (base : ℕ)
    (archive : (ports j).archive=PriorResetArchive.reset v base)
    (layout : (ports j).rangeLayout=v.rangeLayout) (bitsAt : (ports j).operandBits=v.nodeBits)
local notation "okAt" => room path whole ⟨.here,rfl⟩
local notation "regLayout" => (ports j).rangeLayout
local notation "occupant" x => Reached.NodeCells.coordinate now (x).1
local notation "cellOrder" => trajectory p hp a number path whole
local notation "siteType" => NodeOrder.All (path.archive p hp a whole).bit

include archive layout bitsAt in
private theorem finalRegisterCoordinates :
    ∃ (live : 0 < v.receiver.lanes) (blockOf : siteType → Fin v.receiver.blocks)
      (hostOf : siteType → Fin v.receiver.hosts) (groupOf : siteType → Fin v.receiver.groups)
      (numberOf : siteType → Fin v.nodes),
      (∀x, (blockOf x).val = (occupant x).2.2.val ∧ (hostOf x).val = (occupant x).1.val ∧
        (groupOf x).val = (occupant x).2.1.val ∧ (numberOf x).val = (cellOrder x.1 x.2).val) ∧
      registeredPages hp a number path ports memory room path whole =
        fromRAM (PriorResetArchive.reset v base) v.rangeLayout v.nodeBits (memory j)
          live blockOf hostOf groupOf numberOf := by
  have read := registeredPages_final_reset hp a number path ports memory room whole v base archive layout bitsAt
  refine ⟨_,_,_,_,_,?_,read⟩
  intro x
  exact ⟨rfl,rfl,rfl,rfl⟩
end
end Hierarchy.DescentSixParty.Chronology.DatePorts

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentColonies DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentGL DescentCompiler DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "cert" => SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "digits" => S.initialDigits ordinary.radix
local notation "q" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)

local notation "actual" => issued X G S ordinary reset branch positive room shorten
local notation "price" => S.epochPower^S.priceExponent
local notation "epsilon" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)


open Chronology.RegisterTimeline DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
variable {w boardSize boardDegree : ℕ} (board : NonlinearExpanders.Graph boardSize boardDegree)
    (op : RotorSpec) (dateTail drift degree payload header : ℕ) (seats profile : ℕ→ℕ)
    (runtime : ℕ→Dated.Ordinary) (initialPos : Position) (c : (Epochs.finish G _ _ (SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice)
local notation "menu" => (⟨board,op,g,dateTail,p,f,drift,degree,payload,seats,runtime,profile,header⟩:Menu boardSize boardDegree)
local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "dateAt" => calendar (w:=w) traces menu initialPos
local notation "steps" => RegisterTimeline.issued (w:=w) traces menu
local notation "selected" => actual c
attribute [local irreducible] SeedNamed.issued

variable (fixed :
    let entries := traceAt X G S ordinary reset branch positive room shorten
    let book : Menu boardSize boardDegree :=
      ⟨board, op, g, dateTail, p, f, drift, degree, payload, seats, runtime, profile, header⟩
    ∀ i (a z : RunTrace.Events entries i) (x y : Move w),
      let pos := calendar (w:=w) entries book initialPos i
      RegisterTimeline.issued entries book i a pos x →
        RegisterTimeline.issued entries book i z pos y → x = y)
variable (start : Rooms G S
    ⟨board, op, g, dateTail, p, f, drift, degree, payload, seats, runtime, profile, header⟩ k w 0 initialPos)
variable (installed :
    let entries := traceAt X G S ordinary reset branch positive room shorten
    let book : Menu boardSize boardDegree :=
      ⟨board, op, g, dateTail, p, f, drift, degree, payload, seats, runtime, profile, header⟩
    ∀ i (e : RunTrace.Events entries i),
      let pos := calendar (w:=w) entries book initialPos i
      Rooms G S book k w i pos →
        ∃ move : Move w, RegisterTimeline.issued entries book i e pos move ∧
          move.next.floor < 2^w ∧
          (e.2.isReset = true → 8 * book.receiverWidth G S k i pos.ports ≤ payload))
variable (originSize : Fintype.card ((issued X G S ordinary reset branch positive room shorten) c).origin.source.V≤ initialPos.ports.operandHosts)
    (originK : initialPos.ports.venue.k=k)
local notation "pinType" => Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width))
local notation "pinBits" => fun _ : pinType=>s*1

set_option maxHeartbeats 1000000 in
include fixed start installed originSize originK in
theorem issued_prefix_operand_geometry {U : MarkedWorld F 0 pinType pinBits} {i z D : ℕ}
    {r : Reached U G q epsilon S k i z D price s}
    (prefix_ : Path (selected).origin.source r) (suffix_ : Path r (selected).target)
    (joined : prefix_.append suffix_=(selected).path) :
    Fintype.card r.V≤(dateAt i).ports.operandHosts ∧ (dateAt i).ports.venue.k=k :=by
  let prefixAt : Path (traces c).first r := by
    dsimp only [traceAt]
    exact prefix_
  let suffixAt : Path r (traces c).last := by
    dsimp only [traceAt]
    exact suffix_
  have joinedAt : prefixAt.append suffixAt = (traces c).path := by
    dsimp only [traceAt, prefixAt, suffixAt]
    exact joined
  have originAt : Fintype.card (traces c).first.V ≤ initialPos.ports.operandHosts := by
    dsimp only [traceAt]
    exact originSize
  refine @RegisterTimeline.operandGeometryOnTrace F pinType _ G S pinBits 0 k price s S.length w q epsilon
    _ traces boardSize boardDegree menu initialPos fixed start installed c originAt originK ?_ U i z D r
    prefixAt suffixAt joinedAt
  intro V age grain degree₀ grain' degree' rate src nonneg T ballot norm dst ticket prev rest eqn at_
  dsimp only [traceAt] at prev rest eqn
  exact @Branch.registered_ordinary_card F _ cp nP X G S k n h C f g p _ _ _ ordinary.radix run c
    (selected) V age grain degree₀ grain' degree' rate src T nonneg ballot norm dst ticket prev rest eqn
    op dateTail drift degree payload (seats age) at_.ports runtime at_.floor


variable (args roles : ℕ)
    (seed : initialPos.ports.ArchiveDensity (S.groupCount 0) payload args roles)
    (numbers :
    let entries := traceAt X G S ordinary reset branch positive room shorten
    let book : Menu boardSize boardDegree :=
      ⟨board, op, g, dateTail, p, f, drift, degree, payload, seats, runtime, profile, header⟩
    ∀ i (e : RunTrace.Events entries i),
      let pos := calendar (w:=w) entries book initialPos i
      Rooms G S book k w i pos → OutputPitches entries book i e pos args roles)
    (hPos : 0<payload) (popPos : ∀j,0<S.groupCount j) (agePos : 0<S.height)

include fixed start installed originSize originK seed numbers hPos popPos agePos in
theorem issued_range_room {U : MarkedWorld F 0 pinType pinBits} {i z D : ℕ}
    {r : Reached U G q epsilon S k i z D price s}
    (prefix_ : Path (selected).origin.source r) (whole : prefix_.whole p)
    (extend : ∃suffix_ : Path r (selected).target,prefix_.append suffix_=(selected).path) :
    DatePorts.RangeRoom (dateAt i).ports r (prefix_.archive p positive (selected).origin.archive whole).bit :=by
  obtain ⟨suffix_,joined⟩:=extend
  let prefixAt : Path (traces c).first r := by
    dsimp only [traceAt]
    exact prefix_
  let suffixAt : Path r (traces c).last := by
    dsimp only [traceAt]
    exact suffix_
  have joinedAt : prefixAt.append suffixAt = (traces c).path := by
    dsimp only [traceAt, prefixAt, suffixAt]
    exact joined
  have data := rooms_prefix traces menu initialPos fixed start installed c (U:=U) (r:=r)
    prefixAt suffixAt joinedAt
  have bus := issued_prefix_pitch traces menu initialPos fixed start installed args roles seed numbers
    c (U:=U) (r:=r) prefixAt suffixAt joinedAt hPos popPos
  have live := issued_prefix_operand_geometry X G S ordinary reset branch positive room shorten board op
    dateTail drift degree payload header seats profile runtime initialPos c fixed start installed originSize originK
    (U:=U) (i:=i) (z:=z) (D:=D) (r:=r) prefix_ suffix_ joined
  exact Branch.prefix_range_room X G S (selected) positive agePos prefix_ suffix_ joined whole (dateAt i).ports
    op dateTail drift degree payload args roles data.archive data.population bus live.2 live.1

local notation "allRooms" => issued_range_room X G S ordinary reset branch positive room shorten board op
  dateTail drift degree payload header seats profile runtime initialPos c fixed start installed originSize originK args roles
  seed numbers hPos popPos agePos
local notation "originalMemory" m => DateCode.history (RunTrace.machine traces (fun t _=>instruction (w:=w) traces menu initialPos t)) m

open private Origin.archiveOrder from OAI.Hierarchy.DescentNamedPrivateArchive
attribute [local irreducible] Origin.archivePackage Origin.source

/-- The original chosen tape, local archive order and native finite-cut execution determine
every range register used by the copy induction. -/
def issuedRangePages (boot : Memory w) {U : MarkedWorld F 0 pinType pinBits} {i z D : ℕ}
    {r : Reached U G q epsilon S k i z D price s} (prefix_ : Path (selected).origin.source r)
    (whole : prefix_.whole p) :=
  DatePorts.registeredPages (start:=(selected).origin.source) (now:=(selected).target) positive (selected).origin.archive (Origin.archiveOrder (selected).origin) (selected).path
    (fun t=>(dateAt t).ports) (originalMemory boot) (fun {U i z D r} pf wh ext => issued_range_room X G S ordinary reset branch positive room shorten board op
  dateTail drift degree payload header seats profile runtime initialPos c fixed start installed originSize originK args roles
  seed numbers hPos popPos agePos (U:=U) (i:=i) (z:=z) (D:=D) (r:=r) pf wh ext) (r:=r) prefix_ whole

open DescentRetainedRangeDigits DescentLocalArchiveOrder DescentKernelHistory DescentDatedPriorOperand
local notation "lastAge" => S.length-1
local notation "oldPos" => dateAt lastAge
local notation "prevFloor" => (oldPos).ports.priorStart k (oldPos).floor
local notation "lastJob" => PhysicalReset.scheduledAtPorts G S board k dateTail lastAge p f g drift degree payload runtime op
  (S.firstWidth G.b p) (S.grainAt G.b p 0) (oldPos).ports (oldPos).floor
local notation "resetOut" => (lastJob).inner.successor
local notation "resetBase" => (lastJob).inner.rebased ((lastJob).inner.stageStart prevFloor)
local notation "wh" => (selected).path.recorded_whole p (selected).recorded
local notation "allNodes" => NodeOrder.All (Branch.archive X G S (selected) positive).bit
local notation "atNode" x => Reached.NodeCells.coordinate (selected).target (x).1
local notation "activePages" => issuedRangePages X G S ordinary reset branch positive room shorten board op dateTail drift
  degree payload header seats profile runtime initialPos c fixed start installed originSize originK args roles seed numbers hPos popPos agePos

set_option maxHeartbeats 1000000 in
/-- The register on the very last original tape has exactly the reset-returned rectangle,
with every coordinate numerically the genuine named vertex, group, block and local primitive number. -/
theorem issued_final_range_register (boot : Memory w) :
    ∃(live : 0<(resetOut).receiver.lanes) (blockOf : allNodes→Fin (resetOut).receiver.blocks)
      (hostOf : allNodes→Fin (resetOut).receiver.hosts) (groupOf : allNodes→Fin (resetOut).receiver.groups)
      (numberOf : allNodes→Fin (resetOut).nodes),
      (∀x, (blockOf x).val=(atNode x).2.2.val ∧ (hostOf x).val=(atNode x).1.val ∧
        (groupOf x).val=(atNode x).2.1.val ∧ (numberOf x).val=(Branch.localNodes X G S (selected) positive x.1 x.2).val) ∧
      (activePages) boot (selected).path wh=
        fromRAM (PriorResetArchive.reset resetOut resetBase) (resetOut).rangeLayout (resetOut).nodeBits
          ((originalMemory boot) S.length) live blockOf hostOf groupOf numberOf := by
  let ending := issuedFinalReset X G S ordinary reset branch positive room shorten c agePos
  have key := @RegisterTimeline.venueKeyOnEvent F pinType _ G S pinBits 0 k price s S.length w q epsilon
    _ traces boardSize boardDegree menu initialPos c (by
      intro U i z D r pr sf joined
      dsimp only [traceAt] at pr sf joined
      exact (issued_prefix_operand_geometry X G S ordinary reset branch positive room shorten board op
        dateTail drift degree payload header seats profile runtime initialPos c fixed start installed
        originSize originK (U:=U) (r:=r) pr sf joined).2) lastAge ending.event
  let returned := @RegisterTimeline.finalRegisteredFields F pinType _ G S pinBits 0 k price s S.length w q epsilon
    _ traces boardSize boardDegree menu initialPos fixed start installed c p ending key
  let registerData := @DatePorts.finalRegisterCoordinates F pinType _ 0 pinBits G q epsilon S k price s w
    _ _ 0 _ _ S.length _ _ (selected).origin.source (selected).target p
    positive (selected).origin.archive (Origin.archiveOrder (selected).origin) (selected).path
    (fun t=>(dateAt t).ports) (originalMemory boot)
    (fun {U i z D r} pf wholeAt extendsAt => issued_range_room X G S ordinary reset branch positive room shorten board op
      dateTail drift degree payload header seats profile runtime initialPos c fixed start installed originSize originK
      args roles seed numbers hPos popPos agePos (U:=U) (r:=r) pf wholeAt extendsAt) wh resetOut resetBase
    returned.1 returned.2.1 returned.2.2
  dsimp only [Branch.archive,Branch.localNodes,issuedRangePages]
  exact registerData

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
