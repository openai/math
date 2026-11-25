import OAI.Hierarchy.DescentIssuedSeedTaggedStart
import OAI.Hierarchy.DescentNamedSeedPosition
import OAI.Hierarchy.DescentNamedPrivateArchive
import OAI.Hierarchy.DescentNamedSeedLocalNodes
import OAI.Hierarchy.DescentDatedSeedOriginalCoordinates
import OAI.Hierarchy.DescentSeedPointerWidths
import OAI.Hierarchy.DescentDatedSeedAppendedProfile

namespace OAI
/-! The three original seed register receipts on the ballot which reaches the selected branch. -/
namespace Hierarchy.DescentDatedSeedStartup.SeedHeader.Input
open DescentCompiler DescentSixParty DescentInitialHost DescentSeedRoot Catalyst
open DescentSixParty.SeedNamed DescentSixParty.Chronology DescentSixParty.Chronology.RegisterTimeline
open DescentKernelHistory DescentPrimitivePalette DescentColonies DescentRotor
open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall DescentWideSeedFlags
open DescentExterior DescentExteriorShelf DescentGL Computability.BorderVNP.Crossing Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 1000000
open private oneNodeEach from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates
open private Origin.archiveOrder from OAI.Hierarchy.DescentNamedPrivateArchive
open DescentLocalArchiveOrder DescentDatedSeedStartup

attribute [local irreducible] Origin.source Origin.archivePackage

private theorem roomFromFields {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ}
    {U : MarkedWorld F d P bits} {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ}
    {k i z D wire hist : ℕ} (ports : DatePorts) (r : Reached U G q ε S k i z D wire hist)
    (A : Archive U) (one : oneNodeEach A)
    (nodeRoom : 1 ≤ ports.nodes) (hostRoom : @Fintype.card r.V r.finite ≤ ports.operandHosts)
    (groups : S.groupCount i=ports.venue.groups) (radix : k=ports.venue.k) (lanes : 0<ports.operandLanes) :
    DatePorts.RangeRoom ports r A.bit :=
  ⟨fun u => (one u).le.trans nodeRoom,
   fun u => (r.vertex (r.placement.pos u).2).isLt.trans_le hostRoom, groups, radix, lanes⟩

open DescentBundleHistory DescentPackedSeed
open private Origin.archive_eq from OAI.Hierarchy.DescentNamedPrivateArchive

private theorem selectedSingleton {F P : Type} [Field F] {d : ℕ} {bits : P → ℕ}
    {U V : MarkedWorld F d P bits} (a : Archive U)
    (v : Equiv.Perm U.graph.Site) (e : Equiv.Perm U.graph.Edge)
    (pkg : ArchiveTransport (renamedArchive a v e) V) (one : oneNodeEach a) :
    oneNodeEach pkg.data := by
  have renamed : oneNodeEach (renamedArchive a v e) := fun u => one (v.symm u)
  exact (pkg.carry (fun _ b => PLift (oneNodeEach b)) ⟨renamed⟩).down

private theorem singletonOfEq {F P : Type} [Field F] {d : ℕ} {bits : P → ℕ}
    {U : MarkedWorld F d P bits} (a b : Archive U) (h : a=b) (one : oneNodeEach a) :
    oneNodeEach b := h ▸ one
private theorem nativeSeedSingleton {F : Type} [Field F] {S : AtomSchedule} {D : PoweredGadget F}
    {k cp np wire grain Z : ℕ} (X : Approximation F cp np) {q ε : ℝ}
    {c : (initialGroup X S.copies grain).Choice} {digits : Fin S.copies ≃ Fin (S.groupCount 0) × Block k}
    (o : Origin (G:=D) (S:=S) (q:=q) (fee:=ε) (z:=Z) (wire:=wire) X c digits) :
    oneNodeEach o.archive :=
  singletonOfEq o.archivePackage.data o.archive (Origin.archive_eq o).symm
    (selectedSingleton (seedArchive X S.copies grain c) (site o.raw) (edge o.raw)
      o.archivePackage (initial_nodes X S.copies grain c))

private theorem seedOriginRange {F : Type} [Field F] {S : AtomSchedule} (D : PoweredGadget F)
    (op : RotorSpec) {k cp np H wire : ℕ} (X : Approximation F cp np) (l : Layout)
    (radix : S.radix=2^k) (payload Z : ℕ) {q ε : ℝ} {c : (initialGroup X S.copies l.seedWidth).Choice}
    (o : Origin X (s:=l.seedWidth) (G:=D) (S:=S) (q:=q) (fee:=ε) (z:=Z) (wire:=wire) c (S.initialDigits radix))
    (wide : Fintype.card o.raw.V≤H) (positive : 0<l.operandLanes) :
    DatePorts.RangeRoom (DatePorts.initial D op X S.copies l k H (S.groupCount 0) payload Z)
      o.source o.archive.bit := by
  exact roomFromFields _ o.source o.archive (nativeSeedSingleton X o)
    (Nat.le_refl 1) (source_hosts X o wide) rfl rfl positive

variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec) (t f g drift : ℕ) (v : SeedHeader.Input F)
    (h : ℕ) {w : ℕ}
local notation "l" => v.layout G t f g drift h
local notation "s" => (l).seedWidth
local notation "header" => v.base G h-1
local notation "lo" => selectorBase v.circuit v.schedule.copies s h v.steps.length
local notation "pitch" => DescentPackedEpochShelves.grain (h/2) G.C
local notation "origin" => end_ (lo+extent pitch v.steps) G.C pitch
local notation "E" => ExteriorCount v.circuit
local notation "front" => publicFront v.circuit v.schedule.copies s h G.C v.steps v.j v.rest
local notation "extra" => v.appendix.words (E*2^(v.j+v.rest))
local notation "Z" => v.schedule.grainAt G.b v.p 0
local notation "M" => Primitive.paletteLanes G op s Z h v.k

variable (radix : v.schedule.radix=2^v.k) (hosts : Fintype.card (Vertex v.circuit)≤v.hosts)
    (seed : Select v.circuit v.schedule.copies ((v.layout G t f g drift h).seedWidth)→v.labels)
    (x : Fin (ExteriorCount v.circuit)→Plane v.j v.rest→Fin ((v.layout G t f g drift h).seedWidth)→Bool) (z : v.labels⊕Hidden (ExteriorCount v.circuit) v.j v.rest ((v.layout G t f g drift h).seedWidth)→Bool) (back : Memory w)
local notation "raw" => Root.appended (origin+17*DescentExteriorShelf.span v.j v.rest s E) extra
  (Root.widePackedImage v.circuit v.schedule.copies s h w seed lo G.C pitch v.steps origin x z) back
local notation "checked" => countedAt v.circuit v.schedule.copies s h seed (z∘Sum.inl) raw
local notation "done" => DescentDatedSeedStartup.Input.completeImage G op v.circuit (v.schedule.initialDigits radix)
  hosts l header h Z checked

local notation "flag" => DescentWideSeedFlags.endInput v.circuit v.schedule.copies s h
local notation "rows₀" => DescentPackedSeed.rows v.circuit v.schedule.copies s h
local notation "finish" => (DescentDatedSeedStartup.Input.nodeChart l v.k v.hosts (v.schedule.groupCount 0)).seedEnd
  (DescentDatedSeedStartup.endAddress v.circuit l v.hosts (v.schedule.groupCount 0) v.k)
local notation "start" => (⟨DatePorts.initial G op v.circuit v.schedule.copies l v.k v.hosts (v.schedule.groupCount 0) h Z,
  Primitive.initialEnd v.circuit v.schedule.copies s h v.k v.hosts (v.schedule.groupCount 0) M finish⟩ : RegisterTimeline.Position)
local notation "pins" => Σ _ : Fin v.schedule.copies,Fin (Fintype.card (Port v.pins v.circuit.width))
local notation "portion" => (fun _ : pins=>s*1)
variable {q ε : ℝ} {wire epoch z' D' R : ℕ} {c : (initialGroup v.circuit v.schedule.copies s).Choice}
    (o : Origin v.circuit («s»:=(v.layout G t f g drift h).seedWidth) («G»:=G) (S:=v.schedule) (q:=q) (fee:=ε) (z:=Z) (wire:=wire) c (v.schedule.initialDigits radix))
    (hp : 0<v.p) (units : 1≤R) (menu : Runnable F op)
    {lastWorld : MarkedWorld F 0 pins portion} (target : Reached lastWorld G q ε v.schedule v.k epoch z' D' wire s)
    (path : Path o.source target)

theorem seed_grain_dvd (sched : AtomSchedule) (b p : ℕ) : p∣sched.firstWidth b p :=
  dvd_mul_of_dvd_left (dvd_mul_right p _) b

private theorem positionedSeedDvd : v.p ∣ (l).seedWidth :=
  seed_grain_dvd v.schedule G.b v.p

private theorem taggedSelectorFloor : flag+(rows₀+1)≤lo := by
  dsimp only [selectorBase]
  omega

private theorem taggedFrontFloor : lo≤front := by
  dsimp only [publicFront,end_,dict]
  omega

private theorem taggedHeaderFloor : header<(l).base := by
  change v.base G h-1<v.base G h
  dsimp only [SeedHeader.Input.base]
  omega

attribute [local irreducible] Origin.archiveOrder DescentDatedSeedStartup.Input.issuedSeedClaimAtFirst
local notation "claim" => @DescentDatedSeedStartup.Input.issuedSeedClaimAtFirst F _ v.schedule G op
  v.k v.arity v.pins w v.circuit radix l Z q ε wire c o menu (Origin.archiveOrder o) v.p R hp units
  (positionedSeedDvd G t f g drift v h) epoch z' D' lastWorld target path

/-- The selected width, operand pitch and actual decoded ballot start the chronological
archive. Occupied nodes use their original singleton rank, and the initialized pages also
cover every unused slot and every source site outside the paid census. -/
theorem position_tagged_words (digits : 16*digitsNeeded s≤h) (live : 0<M) (machine : h≤w)
    (printed : DescentPrimitivePalette.printedBits G s Z op*M≤w)
    (signed : DescentSignedCableCodec.width 3 256*(l).packedLanes≤w) (fieldWord : (l).operandBits*(l).operandLanes≤w)
    (fit : s<2^Nat.clog 2 (s+1)) (space : (start).floor<2^w)
    (groups : v.schedule.baseGroups=2^v.tail) (epochs : 0<v.schedule.height) (budget : G.b≤2^v.schedule.capGain)
    (positive : 0<(l).operandLanes) (decoded : decode v.circuit ((z∘Sum.inl)∘seed)=some c) :
    (start).ports.held o.source (start).floor done ∧ claim start done ∧ (start).ports.ArchiveTags done :=by
  have wide : Fintype.card o.raw.V≤v.hosts:=o.seed.hostSize.le.trans hosts
  have register := seedOriginRange G op v.circuit l radix h Z o wide positive
  have before := taggedSelectorFloor G t f g drift v h
  have frontLow := taggedFrontFloor G t f g drift v h
  have reserved := (v.header_after_votes G h).1
  have early := taggedHeaderFloor G t f g drift v h
  have alloc:=fences v.circuit l v.hosts (v.schedule.groupCount 0) v.k
  have floorSeed : (l).base≤finish:=
    (alloc.1.trans (alloc.2.1.trans alloc.2.2)).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have last:=Primitive.fences v.circuit v.schedule.copies s h v.k v.hosts (v.schedule.groupCount 0) M finish
  have above : finish≤(start).floor:=last.1.trans last.2
  have flagLow : flag+(rows₀+1)≤(l).base:=
    before.trans (frontLow.trans ((Nat.le_add_right ..).trans (reserved.trans early.le)))
  have fits:=flagLow.trans_lt (floorSeed.trans_lt (above.trans_lt space))
  have source:=Root.role_source_extent v.circuit v.schedule.copies s h digits
  have initial : flag≤finish:=(Nat.le_add_right ..).trans (flagLow.trans floorSeed)
  have fieldBounds:=selected_pointer_widths G v.schedule h v.k v.tail g v.p drift v.degree f (quota t)
    (v.base G h) (v.schedule.censusBits v.p) v.wire v.hist groups radix epochs budget
  exact DescentDatedSeedStartup.Input.issued_startup_tagged G op v.circuit radix hosts l header h Z
    seed lo G.C pitch v.steps origin extra x z back o wide menu (Origin.archiveOrder o) register hp units
    (positionedSeedDvd G t f g drift v h) target path digits live machine printed fit
    decoded signed fieldWord fits before le_rfl reserved early space (source.trans initial)
    fieldBounds.1 fieldBounds.2.1 fieldBounds.2.2 rfl

end
end Hierarchy.DescentDatedSeedStartup.SeedHeader.Input

end OAI
