import OAI.Hierarchy.DescentSeedArchiveHeaders
import OAI.Hierarchy.DescentSeedArchiveSpans
import OAI.Hierarchy.DescentSeedArchivePrimitive

namespace OAI
/-! # Complete original archive on the first emitted register -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler Catalyst DescentInitialHost DescentPackedSeed DescentDatedSeedStartup
open DescentKernelHistory DescentRetainedRangeDigits DescentLocalArchiveOrder SeedNamed Computability.BorderVNP.Crossing
open DescentSeedRoot DescentSeedInitialTable DescentColonies DescentDyadicSpan DescentRotor
open DescentDatedSeedStartup.Input DescentDatedPriorOperand DescentOperandStateBanks
open DescentPrimitivePalette DescentPackedColony DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
open DescentBundleHistory

/-- The five fields of a single archive read can be checked before fixing the seed world. -/
private structure SeedArchiveAssembly where
  headers : Prop
  spans : Prop
  flags : Prop
  arity : Prop
  primitive : Prop
  result : Prop
  assemble : headers → spans → flags → arity → primitive → result

private def SeedArchiveAssembly.ofConstructor {H S F A P R : Prop}
    (build : H → S → F → A → P → R) : SeedArchiveAssembly :=
  ⟨H, S, F, A, P, R, build⟩

private def SeedArchiveAssembly.fromSources (v : SeedArchiveAssembly)
    {H S F A P : Prop} (headers : H → v.headers) (spans : S → v.spans)
    (flags : F → v.flags) (arity : A → v.arity) (primitive : P → v.primitive) :
    SeedArchiveAssembly :=
  SeedArchiveAssembly.ofConstructor (fun (h : H) (s : S) (f : F) (a : A) (p : P) =>
    v.assemble (headers h) (spans s) (flags f) (arity a) (primitive p))

private def archiveReadAssembly {F P : Type} [_root_.Field F] {d : ℕ} {bits : P → ℕ}
    {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule}
    {k age grain degree wire hist p R s Z w : ℕ} (ports : DatePorts)
    (r : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B) (shape : WorldShape p R B)
    (op : RotorSpec) (label : NodeOrder.All B → Label G s Z op)
    (pointer : NodeOrder.All B → ℕ → Pointer)
    (flags : Fin (2^ports.venue.k) → Fin ports.nodes → Fin ports.operandHosts → Fin ports.venue.groups → ℕ)
    (m : Memory w) : SeedArchiveAssembly :=
  SeedArchiveAssembly.ofConstructor
    (ArchiveRead.mk (ports := ports) (r := r) (B := B) (number := number) (room := room)
      (shape := shape) (op := op) (label := label) (pointer := pointer) (flags := flags) (m := m))

open private transportArchive from OAI.Hierarchy.DescentNamedOriginalArchive in
private def namedReadAssembly {F P : Type} [_root_.Field F] [Fintype P] {d : ℕ} {bits : P → ℕ}
    {W W' : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule}
    {k grain wire hist p R s Z w : ℕ} (ports : DatePorts)
    (r : Reached W G q ε S k 0 grain 3 wire hist) (ar : Archive W) (eqn : world r = W')
    (hp : 0 < p) (sh : WorldShape p R ar.bit) (inputPin : P → ℕ)
    (op : RotorSpec) {dict : Label G s Z op → List (List Bool) → F}
    (code : Encoding (Label G s Z op) dict ar.bit) :=
  let pkg := transportArchive (renamedArchive ar (site r) (edge r)) eqn
  let current := SeedNamed.transport r eqn
  let installed := pkg.carry (fun _ b => WorldShape p R b.bit) (sh.renamed (site r) (edge r))
  let labels := (Palette.transported r ar eqn code).atNode
  fun (nr : Local pkg.data.bit) (ok : RangeRoom ports current pkg.data.bit) (m : Memory w) =>
    archiveReadAssembly ports current pkg.data.bit nr ok installed op labels
      (Reached.argumentPointer current pkg.data.bit nr installed hp inputPin ports.argumentsPerNode)
      (RegisterTimeline.archiveFlag current pkg.data.bit nr ports ok) m

section PhysicalSources

open private namedArchiveGeometry OrderedSlotGeometry.ordering OrderedSlotGeometry.room
  from OAI.Hierarchy.DescentDatedSeedSlotGeometry
open private SeedNamed.FromPublicKeys SeedNamed.Origin.rawArgumentClaim
  from OAI.Hierarchy.DescentSeedRenamedPointers
open private physicalHeaderProgram HeaderProgram.rows HeaderRows.read
  from OAI.Hierarchy.DescentSeedArchiveHeaders
open private physicalSpanDigits SpanDigits.atCell
  from OAI.Hierarchy.DescentSeedArchiveSpans

open private physicalCells PrimitiveCells.atSlot
  from OAI.Hierarchy.DescentSeedArchivePrimitive
open private physicalFlagWords physicalArityWords SeedFieldWords.words
  from OAI.Hierarchy.DescentDatedSeedArchiveFlags
variable {F P : Type} [_root_.Field F] [Fintype P] {d : ℕ} {bits : P → ℕ}
    {W W' : MarkedWorld F d P bits} (G : PoweredGadget F) {q fee : ℝ}
    {S : AtomSchedule} {k wire cp pins H : ℕ}
    (X : Approximation F cp pins) (digits : Fin S.copies ≃ Fin (S.groupCount 0) × Block k)
    (publicWide : Fintype.card (Vertex X) ≤ H) (op : RotorSpec) (menu : Runnable F op) (l : DescentDatedSeedStartup.Layout)
    (payload Z : ℕ) {choice : (initialGroup X S.copies l.seedWidth).Choice}
    (r : Reached W G q fee S k 0 Z 3 wire l.seedWidth) (ar : Archive W) (eqn : world r = W')
    (oldSites : NodeOrder.All ar.bit ≃ Fin S.copies × Vertex X)
    (seen : ∀ t : NodeOrder.All ar.bit,
      (r.vertex (r.placement.pos t.1).2).val = (Fintype.equivFin (Vertex X) (oldSites t).2).val ∧
      (r.placement.pos t.1).1 = (digits (oldSites t).1).1 ∧
      r.placement.block t.1 = (digits (oldSites t).1).2)
    (oneNode : ∀ v : W.graph.Site, Fintype.card (ar.bit.recipe v).Node = 1)

local notation "physicalPorts" => initial G op X S.copies l k H (S.groupCount 0) payload Z
local notation "physicalGeometry" => namedArchiveGeometry X digits publicWide op l payload Z
  r ar eqn oldSites seen oneNode

set_option maxHeartbeats 1600000 in
private def physicalReadAssembly {a R : ℕ} (hp : 0 < a) (sh : WorldShape a R ar.bit)
    (inputPin : P → ℕ)
    (oldRaw : NodeOrder.All ar.bit → NodeOrder.All (BitDescription.initial X S.copies l.seedWidth choice))
    (sameSite : ∀ t, oldSites t = ((oldRaw t).1.1, (oldRaw t).1.2))
    (counted : ∀ t : NodeOrder.All ar.bit,
      ((sh.sites t.1).recipe hp).arity t.2 = legArity X (oldRaw t).1.2 * (l.seedWidth/a))
    (pointers : SeedNamed.FromPublicKeys r ar hp inputPin sh
      (fun t => SeedNamed.Origin.rawArgumentClaim (copies := S.copies) (grain := l.seedWidth) (width := a)
        X choice (oldRaw t)))
    (wide : 1 < 2^l.operandBits) (pieces : l.groupsPerNode = l.seedWidth/a)
    (previous : ∀ t : NodeOrder.All ar.bit, ∀ j f, DescentRetainedRangeDigits.atSlot (sh.sites t.1) t.2 j f =
      if j < legArity X (oldSites t).2 * (l.seedWidth/a) then DescentRetainedRangeDigits.value DescentTerminalSliceRuns.whole f else 0)
    (code : Encoding (Label G l.seedWidth Z op) (dictionary G op menu a) ar.bit)
    (oldLabel : ∀ t, code.atNode t = .inl (seedRole X S.copies choice (oldSites t).1 (oldSites t).2))
    (nr : OrderedSlotGeometry.ordering physicalGeometry) (ok : OrderedSlotGeometry.room physicalGeometry)
    {w : ℕ} (m : Memory w) : SeedArchiveAssembly := by
  let headerProgram := physicalHeaderProgram (G := G) (choice := choice)
    X digits publicWide op l payload Z r ar eqn oldSites seen oneNode hp sh inputPin
    oldRaw sameSite counted pointers
  let spanProgram := physicalSpanDigits G op X digits publicWide l payload Z r ar eqn oldSites
    seen oneNode sh wide pieces previous
  let archiveView := namedReadAssembly physicalPorts r ar eqn hp sh inputPin op code nr ok m
  let flags := physicalFlagWords X digits publicWide op l payload Z r ar eqn oldSites seen oneNode
  let countedHere : ∀ t : NodeOrder.All ar.bit,
      ((sh.sites t.1).recipe hp).arity t.2 = legArity X (oldSites t).2 * (l.seedWidth/a) := by
    intro t
    rw [sameSite t]
    exact counted t
  let arity := physicalArityWords X digits publicWide op l payload Z r ar eqn oldSites seen oneNode
    hp sh pieces countedHere
  let primitive := physicalCells G op menu X digits publicWide l payload Z r ar eqn
    oldSites seen oneNode code oldLabel
  refine SeedArchiveAssembly.fromSources archiveView
    (H := ∀ (x : Block k) (j : Fin (physicalPorts).argumentsPerNode) (f : Fin 4),
      HeaderRows.read (HeaderProgram.rows headerProgram nr ok) m x j f)
    (S := ∀ (x : Block k) (j : Fin (physicalPorts).argumentsPerNode) (f : Fin 3),
      ∃ cells : Fin H → Fin (S.groupCount 0) → Cell (l.operandBits * 1),
        Reads (previousBank (physicalPorts).rangeLayout (physicalPorts).archive.arguments x
          (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) j)) cells l.operandLanes m ∧
        ∀ h g, SpanDigits.atCell spanProgram nr ok x j f h g (cells h g))
    (F := ∀ x : Block k, Reads (metadataPage physicalPorts 0 x)
      (SeedFieldWords.words flags nr ok x) l.operandLanes m)
    (A := ∀ x : Block k, Reads (metadataPage physicalPorts 1 x)
      (SeedFieldWords.words arity nr ok x) l.operandLanes m)
    (P := ∀ x : Block k, Reads ((physicalPorts).archive.roles.bank x.val)
      (fun h g => encode (printedBits G l.seedWidth Z op) 1 (PrimitiveCells.atSlot primitive nr ok x h g))
      (physicalPorts).roleLanes m)
    ?_ ?_ (fun h => h) (fun h => h) (fun h => h)
  · intro paid x j f
    obtain ⟨cells, read, agrees⟩ := paid x j f
    refine ⟨cells, read, ?_⟩
    intro h g n y hit valid
    exact agrees h g n y hit valid
  · intro paid x j f
    obtain ⟨cells, read, agrees⟩ := paid x j f
    refine ⟨cells, read, ?_⟩
    intro h g n y hit valid
    exact agrees h g n y hit valid


set_option maxHeartbeats 1600000 in
private theorem physicalRead {a R : ℕ} (hp : 0 < a) (sh : WorldShape a R ar.bit)
    (inputPin : P → ℕ)
    (oldRaw : NodeOrder.All ar.bit → NodeOrder.All (BitDescription.initial X S.copies l.seedWidth choice))
    (sameSite : ∀ t, oldSites t = ((oldRaw t).1.1, (oldRaw t).1.2))
    (counted : ∀ t : NodeOrder.All ar.bit,
      ((sh.sites t.1).recipe hp).arity t.2 = legArity X (oldRaw t).1.2 * (l.seedWidth/a))
    (pointers : SeedNamed.FromPublicKeys r ar hp inputPin sh
      (fun t => SeedNamed.Origin.rawArgumentClaim (copies := S.copies) (grain := l.seedWidth) (width := a)
        X choice (oldRaw t)))
    (wide : 1 < 2^l.operandBits) (pieces : l.groupsPerNode = l.seedWidth/a)
    (previous : ∀ t : NodeOrder.All ar.bit, ∀ j f, DescentRetainedRangeDigits.atSlot (sh.sites t.1) t.2 j f =
      if j < legArity X (oldSites t).2 * (l.seedWidth/a) then DescentRetainedRangeDigits.value DescentTerminalSliceRuns.whole f else 0)
    (code : Encoding (Label G l.seedWidth Z op) (dictionary G op menu a) ar.bit)
    (oldLabel : ∀ t, code.atNode t = .inl (seedRole X S.copies choice (oldSites t).1 (oldSites t).2))
    (nr : OrderedSlotGeometry.ordering physicalGeometry) (ok : OrderedSlotGeometry.room physicalGeometry)
    {w : ℕ} (m : Memory w) :
  let headerProgram := physicalHeaderProgram (G := G) (choice := choice)
    X digits publicWide op l payload Z r ar eqn oldSites seen oneNode hp sh inputPin
    oldRaw sameSite counted pointers
  let spanProgram := physicalSpanDigits G op X digits publicWide l payload Z r ar eqn oldSites
    seen oneNode sh wide pieces previous
  let flags := physicalFlagWords X digits publicWide op l payload Z r ar eqn oldSites seen oneNode
  let countedHere : ∀ t : NodeOrder.All ar.bit,
      ((sh.sites t.1).recipe hp).arity t.2 = legArity X (oldSites t).2 * (l.seedWidth/a) := by
    intro t
    rw [sameSite t]
    exact counted t
  let arity := physicalArityWords X digits publicWide op l payload Z r ar eqn oldSites seen oneNode
    hp sh pieces countedHere
  let primitive := physicalCells G op menu X digits publicWide l payload Z r ar eqn
    oldSites seen oneNode code oldLabel
  (∀ (x : Block k) (j : Fin (physicalPorts).argumentsPerNode) (f : Fin 4),
    HeaderRows.read (HeaderProgram.rows headerProgram nr ok) m x j f) →
  (∀ (x : Block k) (j : Fin (physicalPorts).argumentsPerNode) (f : Fin 3),
    ∃ cells : Fin H → Fin (S.groupCount 0) → Cell (l.operandBits * 1),
      Reads (previousBank (physicalPorts).rangeLayout (physicalPorts).archive.arguments x
        (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) j)) cells l.operandLanes m ∧
      ∀ h g, SpanDigits.atCell spanProgram nr ok x j f h g (cells h g)) →
  (∀ x : Block k, Reads (metadataPage physicalPorts 0 x)
    (SeedFieldWords.words flags nr ok x) l.operandLanes m) →
  (∀ x : Block k, Reads (metadataPage physicalPorts 1 x)
    (SeedFieldWords.words arity nr ok x) l.operandLanes m) →
  (∀ x : Block k, Reads ((physicalPorts).archive.roles.bank x.val)
    (fun h g => encode (printedBits G l.seedWidth Z op) 1 (PrimitiveCells.atSlot primitive nr ok x h g))
    (physicalPorts).roleLanes m) →
  SeedArchiveAssembly.result (physicalReadAssembly (choice := choice) G X digits publicWide op menu l payload Z r ar eqn
    oldSites seen oneNode hp sh inputPin oldRaw sameSite counted pointers wide pieces previous
    code oldLabel nr ok m) :=
  SeedArchiveAssembly.assemble (physicalReadAssembly (choice := choice) G X digits publicWide op menu l payload Z r ar eqn
      oldSites seen oneNode hp sh inputPin oldRaw sameSite counted pointers wide pieces previous
      code oldLabel nr ok m)

open private HeaderProgram.read from OAI.Hierarchy.DescentSeedArchiveHeaders
open private SpanDigits.read from OAI.Hierarchy.DescentSeedArchiveSpans
open private SeedFieldWords.emitted from OAI.Hierarchy.DescentDatedSeedArchiveFlags
open private singleton_reads PrimitiveCells.scalar
  from OAI.Hierarchy.DescentSeedArchivePrimitive

local notation "physicalSeat" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)

set_option maxHeartbeats 1600000 in
private theorem physicalReadFromBanks {a R : ℕ} (hp : 0 < a) (sh : WorldShape a R ar.bit)
    (inputPin : P → ℕ)
    (oldRaw : NodeOrder.All ar.bit → NodeOrder.All (BitDescription.initial X S.copies l.seedWidth choice))
    (sameSite : ∀ t, oldSites t = ((oldRaw t).1.1, (oldRaw t).1.2))
    (counted : ∀ t : NodeOrder.All ar.bit,
      ((sh.sites t.1).recipe hp).arity t.2 = legArity X (oldRaw t).1.2 * (l.seedWidth/a))
    (pointers : SeedNamed.FromPublicKeys r ar hp inputPin sh
      (fun t => SeedNamed.Origin.rawArgumentClaim (copies := S.copies) (grain := l.seedWidth) (width := a)
        X choice (oldRaw t)))
    (wide : 1 < 2^l.operandBits) (pieces : l.groupsPerNode = l.seedWidth/a)
    (previous : ∀ t : NodeOrder.All ar.bit, ∀ j f, DescentRetainedRangeDigits.atSlot (sh.sites t.1) t.2 j f =
      if j < legArity X (oldSites t).2 * (l.seedWidth/a) then DescentRetainedRangeDigits.value DescentTerminalSliceRuns.whole f else 0)
    (code : Encoding (Label G l.seedWidth Z op) (dictionary G op menu a) ar.bit)
    (oldLabel : ∀ t, code.atNode t = .inl (seedRole X S.copies choice (oldSites t).1 (oldSites t).2))
    (nr : OrderedSlotGeometry.ordering physicalGeometry) (ok : OrderedSlotGeometry.room physicalGeometry)
    {w : ℕ} (m : Memory w) (wordRoom : 3 < 2^l.operandBits)
    (copies : S.copies ≤ 2^l.operandBits) (quota : l.groupsPerNode ≤ 2^l.operandBits)
    (pageReads : ∀ (f : DescentOperandStateBanks.Field) (j : Fin (physicalPorts).argumentsPerNode)
      (x : Block k), Reads (previousBank (physicalPorts).rangeLayout (physicalPorts).archive.arguments x
        (DescentOperandStateBanks.page f j))
      (Seed.Physical.value X physicalSeat (Equiv.refl _) digits l.groupsPerNode l.operandBits 1 j.val f x)
      l.operandLanes m)
    (metadata : ∀ (x : Block k) (f : Fin 2), Reads (metadataPage physicalPorts f x)
      ((nodeChart l k H (S.groupCount 0)).seedField (nodeArities X publicWide l) f) l.operandLanes m)
    (tokens : ∀ x : Block k, Reads ((physicalPorts).archive.roles.bank x.val)
      (Primitive.value X G op S.copies l.seedWidth Z k H (S.groupCount 0) physicalSeat choice digits x)
      (physicalPorts).roleLanes m) :
    SeedArchiveAssembly.result (physicalReadAssembly (choice := choice) G X digits publicWide op menu l payload Z r ar eqn
      oldSites seen oneNode hp sh inputPin oldRaw sameSite counted pointers wide pieces previous
      code oldLabel nr ok m) := by
  let headerProgram := physicalHeaderProgram (G := G) (choice := choice)
    X digits publicWide op l payload Z r ar eqn oldSites seen oneNode hp sh inputPin
    oldRaw sameSite counted pointers
  let spanProgram := physicalSpanDigits G op X digits publicWide l payload Z r ar eqn oldSites
    seen oneNode sh wide pieces previous
  let flags := physicalFlagWords X digits publicWide op l payload Z r ar eqn oldSites seen oneNode
  let countedHere : ∀ t : NodeOrder.All ar.bit,
      ((sh.sites t.1).recipe hp).arity t.2 = legArity X (oldSites t).2 * (l.seedWidth/a) := by
    intro t
    rw [sameSite t]
    exact counted t
  let arity := physicalArityWords X digits publicWide op l payload Z r ar eqn oldSites seen oneNode
    hp sh pieces countedHere
  let primitive := physicalCells G op menu X digits publicWide l payload Z r ar eqn
    oldSites seen oneNode code oldLabel
  refine physicalRead (choice := choice) G X digits publicWide op menu l payload Z r ar eqn
    oldSites seen oneNode hp sh inputPin oldRaw sameSite counted pointers wide pieces previous
    code oldLabel nr ok m ?_ ?_ ?_ ?_ ?_
  · intro x j f
    exact HeaderProgram.read headerProgram nr ok ⟨wordRoom,copies,quota,pieces⟩ m x j f
      (pageReads (f.castLE (by decide : 4 ≤ 7)) j x)
  · intro x j f
    let face := DescentRetainedRangeDigits.page f
    refine ⟨Seed.Physical.value X physicalSeat (Equiv.refl _) digits l.groupsPerNode l.operandBits 1
      j.val face x, pageReads face j x, ?_⟩
    exact SpanDigits.read spanProgram nr ok x j f
  · intro x
    exact Eq.subst (motive := fun rows => Reads (metadataPage physicalPorts 0 x) rows l.operandLanes m)
      (SeedFieldWords.emitted flags nr ok x) (metadata x 0)
  · intro x
    exact Eq.subst (motive := fun rows => Reads (metadataPage physicalPorts 1 x) rows l.operandLanes m)
      (SeedFieldWords.emitted arity nr ok x) (metadata x 1)
  · intro x
    exact singleton_reads ((physicalPorts).archive.roles.bank x.val) m
      (Primitive.value X G op S.copies l.seedWidth Z k H (S.groupCount 0) physicalSeat choice digits x)
      (fun n h g => PrimitiveCells.atSlot primitive nr ok x h g n)
      (fun n h g => PrimitiveCells.scalar primitive nr ok x h g n) (tokens x)

end PhysicalSources

variable {F : Type} [_root_.Field F] {S : AtomSchedule} (G : PoweredGadget F) (op : RotorSpec) (menu : Runnable F op)
    {k cp p H : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies≃Fin (S.groupCount 0)×Block k)
    (publicWide : Fintype.card (Vertex X)≤H) (l : DescentDatedSeedStartup.Layout) (header payload Z : ℕ)
local notation "g₀" => S.groupCount 0
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => DescentDatedSeedStartup.endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "finish" => (chart).seedEnd top
local notation "lanes" => DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k
local notation "limit" => DescentDatedSeedStartup.Primitive.initialEnd X S.copies l.seedWidth payload k H g₀ lanes finish
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "ports" => initial G op X S.copies l k H g₀ payload Z
local notation "final" => completeImage G op X digits publicWide l header payload Z

open private originalGeometry OrderedSlotGeometry.ordering OrderedSlotGeometry.room
  from OAI.Hierarchy.DescentDatedSeedSlotGeometry
variable {q ε : ℝ} {wire : ℕ} {choice : (initialGroup X S.copies l.seedWidth).Choice}
    (o : SeedNamed.Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=Z) (wire:=wire) choice digits)
    (ord : OrderedSlotGeometry.ordering (originalGeometry X digits publicWide op l payload Z o))
    (ready : OrderedSlotGeometry.room (originalGeometry X digits publicWide op l payload Z o))
    {a R : ℕ} (hp : 0<a) (units : 1≤R) (whole : a∣l.seedWidth)
local notation "pin" => (fun y : (Σ _ : Fin S.copies,Fin (Fintype.card (Port p X.width)))=>y.1.val)

open private SeedNamed.Origin.seedReadsAt
  from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates in
open private SeedNamed.Origin.rawSeedCounted from OAI.Hierarchy.DescentDatedSeedOriginalNode in
open private SeedNamed.Origin.seedKeysDescribe from OAI.Hierarchy.DescentSeedRenamedPointers in
open private SeedNamed.Origin.readSeedRange from OAI.Hierarchy.DescentSeedNamedRange in
open private SeedNamed.seedLabelAtSource from OAI.Hierarchy.DescentSeedArchivePrimitive in
set_option maxHeartbeats 1000000 in
private def seedReadAssembly {w : ℕ} (wide : 1 < 2^l.operandBits) (pieces : l.groupsPerNode=l.seedWidth/a) :=
  physicalReadAssembly (w := w) (choice := choice) G X digits publicWide op menu l payload Z o.raw
    (seedArchive X S.copies l.seedWidth choice) (linked_world X choice digits o.seed)
    (NodeOrder.seedSites X S.copies l.seedWidth choice) (fun y => SeedNamed.Origin.seedReadsAt o y.1)
    (initial_nodes X S.copies l.seedWidth choice) hp
    (seedRetained X S.copies l.seedWidth hp units whole choice).shape pin id (fun _ => rfl)
    (SeedNamed.Origin.rawSeedCounted X choice hp units whole) (SeedNamed.Origin.seedKeysDescribe o hp units whole)
    wide pieces (SeedNamed.Origin.readSeedRange X choice hp units whole)
    (seeded (G := G) (Z := Z) (p := a) op menu X choice)
    (SeedNamed.seedLabelAtSource (G := G) (z := Z) (p := a) op menu X choice)

local notation "getView" => seedReadAssembly G op menu X digits publicWide l payload Z o hp units whole

open private SeedNamed.Origin.seedReadsAt
  from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates in
open private SeedNamed.Origin.rawSeedCounted from OAI.Hierarchy.DescentDatedSeedOriginalNode in
open private SeedNamed.Origin.seedKeysDescribe from OAI.Hierarchy.DescentSeedRenamedPointers in
open private SeedNamed.Origin.readSeedRange from OAI.Hierarchy.DescentSeedNamedRange in
open private SeedNamed.seedLabelAtSource from OAI.Hierarchy.DescentSeedArchivePrimitive in
open private metadata_read from OAI.Hierarchy.DescentDatedSeedArchiveFlags in
set_option maxHeartbeats 2500000 in
/-- The token premise is the physical seed prelude's dated publication on this
same memory. The two metadata fields and seven operand fields are recovered from
the original startup execution. -/
theorem seed_archive {w : ℕ} (m : Memory w) (fieldRoom : l.operandBits*l.operandLanes≤w)
    (early : header<l.base) (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish)
    (live : 0<lanes) (machine : payload≤w) (space : limit<2^w)
    (wordRoom : 3<2^l.operandBits) (copies : S.copies≤2^l.operandBits)
    (quota : l.groupsPerNode≤2^l.operandBits) (pieces : l.groupsPerNode=l.seedWidth/a)
    (tokens : ∀x : Block k,Reads ((ports).archive.roles.bank x.val)
      (Primitive.value X G op S.copies l.seedWidth Z k H g₀ hs choice digits x)
      (ports).roleLanes ((final) m)) :
    SeedArchiveAssembly.result ((getView) ((by decide : 1 < 3).trans wordRoom) pieces ord ready ((final) m)) := by
  let wide : 1<2^l.operandBits := (by decide : 1 < 3).trans wordRoom
  have pageReads := seed_operand_cells G op X digits publicWide l header payload Z m
    fieldRoom early sourceSpace live machine space
  have metadata := metadata_read X digits publicWide op l payload Z header m
    sourceSpace live machine space
  let assembly := (getView) wide pieces ord ready ((final) m)
  -- Reuse the exact worlds, archive, programs and instances of this seed assembly.
  -- The abstract eliminator has the same initial telescope, followed by the three numerical room bounds and the physical reads.
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let lv ← Lean.Meta.getFVarFromUserName `assembly
      let some term := (← lv.fvarId!.getDecl).value? (allowNondep := true)
        | throwError "expected the local seed assembly"
      let some raw ← Lean.Meta.delta? term.consumeMData (· == ``seedReadAssembly)
        | throwError "expected the checked seed assembly specialization"
      let raw := raw.consumeMData
      unless raw.getAppFn.isConstOf ``physicalReadAssembly do
        throwError "expected the abstract physical assembly"
      let evidence ← #[`wordRoom, `copies, `quota, `pageReads, `metadata, `tokens].mapM fun n => do
        let read ← Lean.Meta.getFVarFromUserName n
        pure read
      let applyRead := Lean.mkConst ``physicalReadFromBanks raw.getAppFn.constLevels!
      goal.assign (Lean.mkAppN applyRead (raw.getAppArgs ++ evidence))

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
