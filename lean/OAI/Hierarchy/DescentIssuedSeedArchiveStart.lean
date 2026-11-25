import OAI.Hierarchy.DescentNamedTerminalSliceLayout
import OAI.Hierarchy.DescentNamedPrimitivePalette
import OAI.Hierarchy.DescentDatedSeedActualTokens
import OAI.Hierarchy.DescentDatedSeedIssuedArchive
import OAI.Hierarchy.DescentSeedLoaderHeld
import OAI.Hierarchy.DescentRegisterArchiveSeedClaim

namespace OAI
/-! # The complete original two-plus-seven field archive after the real seed prelude -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentLocalArchiveOrder DescentPrimitivePalette DescentSixParty.Chronology
open DescentInitialHost DescentCompiler DescentSixParty DescentSixParty.SeedNamed DescentColonies
open Chronology RegisterTimeline DescentRotor DescentSeedRoot DescentPackedSeed DescentPackedColony DescentSIMDLookup DescentSeedInitialTable
open DescentExterior DescentGL DescentTerminalEpochChart DescentPackedEpochShelves DescentExteriorShelf
open DescentPackedProfileInstall Computability.VPVNP.BurstRAM PrivateRAM Catalyst Computability.BorderVNP.Crossing
open private Origin.archiveShape from OAI.Hierarchy.DescentNamedHistoryShape
open private Palette.encodedOrigin from OAI.Hierarchy.DescentNamedPrimitivePalette
open scoped Classical Fin.CommRing
noncomputable section
open DescentBundleHistory DescentKernelHistory
section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P → ℕ} {d k wire hist final w : ℕ} {q ε : ℝ}
def atFirstRegister (t : RunTrace G q ε S k wire hist final bits d) (history : PrefixClaim t w)
    (pos : RegisterTimeline.Position) (mem : Memory w) : Prop :=
  history (show Path t.first t.first from .here) pos mem

private def claimOnPath
    {U V : MarkedWorld F d P bits} {z D z' D' : ℕ}
    (first : Reached U G q ε S k 0 z D wire hist)
    (last : Reached V G q ε S k final z' D' wire hist) (path : Path first last)
    {p R : ℕ} (hp : 0 < p) (hR : 1 ≤ R) (widths : ∀ y, p ∣ bits y)
    (op : RotorSpec) (menu : Runnable F op) (a : Archive U) (o : Local a.bit)
    (shape : WorldShape p R a.bit)
    (names : Encoding (Label G hist z op) (dictionary G op menu p) a.bit) (pin : P → ℕ) :
    PrefixClaim (RunTrace.mk U V z D z' D' first last path) w :=
  archiveClaim (RunTrace.mk U V z D z' D' first last path) hp hR widths op menu a o shape names pin

omit [Fintype P] in
private theorem claimOnPathHere
    {U V : MarkedWorld F d P bits} {z D z' D' : ℕ}
    (first : Reached U G q ε S k 0 z D wire hist)
    (last : Reached V G q ε S k final z' D' wire hist) (path : Path first last)
    {p R : ℕ} (hp : 0 < p) (hR : 1 ≤ R) (widths : ∀ y, p ∣ bits y)
    (op : RotorSpec) (menu : Runnable F op) (a : Archive U) (o : Local a.bit)
    (shape : WorldShape p R a.bit)
    (names : Encoding (Label G hist z op) (dictionary G op menu p) a.bit) (pin : P → ℕ)
    (pos : Position) (mem : Memory w) (room : DatePorts.RangeRoom pos.ports first a.bit)
    (seed : DatePorts.ArchiveRead pos.ports first a.bit o room shape op names.atNode
      (Reached.argumentPointer first a.bit o shape hp pin pos.ports.argumentsPerNode)
      (archiveFlag first a.bit o pos.ports room) mem) :
    claimOnPath first last path hp hR widths op menu a o shape names pin Path.here pos mem :=
  archiveClaim_here (RunTrace.mk U V z D z' D' first last path) hp hR widths op menu a o shape names pos mem pin room seed

end

open private transportArchive from OAI.Hierarchy.DescentNamedOriginalArchive
section RawSeed
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {bits : P→ℕ} {d : ℕ} {W V Last : MarkedWorld F d P bits}
    {D : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ} {k grain wire hist final z' D' w : ℕ}
    (rawNode : Reached W D q ε S k 0 grain 3 wire hist) (a : Archive W) (same : world rawNode=V)
    {p R : ℕ} (hp : 0<p) (hR : 1≤R) (widths : ∀y,p∣bits y) (sh : WorldShape p R a.bit)
    (op : RotorSpec) (menu : Runnable F op) (code : Encoding (Label D hist grain op) (dictionary D op menu p) a.bit)
    (pin : P→ℕ)
local notation "cur_" => SeedNamed.transport rawNode same
local notation "pack_" => transportArchive (renamedArchive a (site rawNode) (edge rawNode)) same
local notation "shapeSeed_" => (pack_).carry (fun _ b=>WorldShape p R b.bit) (sh.renamed (site rawNode) (edge rawNode))
local notation "codeSeed_" => Palette.transported rawNode a same code
variable (nr : Local (transportArchive (renamedArchive a (site rawNode) (edge rawNode)) same).data.bit)
    (target : Reached Last D q ε S k final z' D' wire hist) (path : Path (SeedNamed.transport rawNode same) target)
private def rawClaim : PrefixClaim (RunTrace.mk V Last grain 3 z' D' cur_ target path) w :=
  claimOnPath cur_ target path hp hR widths op menu (pack_).data nr shapeSeed_ codeSeed_ pin
private def rawFirst (pos : Position) (mem : Memory w) : Prop :=
  rawClaim rawNode a same hp hR widths sh op menu code pin nr target path Path.here pos mem

omit [Fintype P] in
private theorem rawClaimHere (pos : Position) (mem : Memory w)
    (room : DatePorts.RangeRoom pos.ports cur_ (pack_).data.bit)
    (read : DatePorts.ArchiveRead pos.ports cur_ (pack_).data.bit nr room shapeSeed_ op (codeSeed_).atNode
      (Reached.argumentPointer cur_ (pack_).data.bit nr shapeSeed_ hp pin pos.ports.argumentsPerNode)
      (archiveFlag cur_ (pack_).data.bit nr pos.ports room) mem) :
    rawFirst rawNode a same hp hR widths sh op menu code pin nr target path pos mem :=
  claimOnPathHere cur_ target path hp hR widths op menu (pack_).data nr shapeSeed_ codeSeed_ pin pos mem room read
omit [Fintype P] in
private theorem nameFirstArchive (dst : Archive V) (sameArchive : (pack_).data = dst)
    (shDst : WorldShape p R dst.bit) (codeDst : Encoding (Label D hist grain op) (dictionary D op menu p) dst.bit)
    (shapeAgrees : HEq shapeSeed_ shDst) (codeAgrees : HEq codeSeed_ codeDst)
    (number : Local dst.bit) (pos : Position) (mem : Memory w)
    (room : DatePorts.RangeRoom pos.ports cur_ dst.bit)
    (recorded : ∀ n : Local (pack_).data.bit, DatePorts.RangeRoom pos.ports cur_ (pack_).data.bit →
      rawFirst rawNode a same hp hR widths sh op menu code pin n target path pos mem) :
    claimOnPath cur_ target path hp hR widths op menu dst number shDst codeDst pin Path.here pos mem := by
  subst dst
  obtain rfl := eq_of_heq shapeAgrees
  obtain rfl := eq_of_heq codeAgrees
  exact recorded number room

end RawSeed


section PhysicalBooking
open DescentRetainedRangeDigits DescentOperandStateBanks ProtocolRAM DescentDyadicSpan
open DatePorts
open private DatePorts.physicalReadAssembly DatePorts.SeedArchiveAssembly.result from OAI.Hierarchy.DescentSeedCompleteArchive
open private DatePorts.namedArchiveGeometry DatePorts.OrderedSlotGeometry.ordering DatePorts.OrderedSlotGeometry.room from OAI.Hierarchy.DescentDatedSeedSlotGeometry
open private SeedNamed.FromPublicKeys SeedNamed.Origin.rawArgumentClaim from OAI.Hierarchy.DescentSeedRenamedPointers
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

local notation "physicalPorts" => DatePorts.initial G op X S.copies l k H (S.groupCount 0) payload Z
local notation "physicalGeometry" => DatePorts.namedArchiveGeometry X digits publicWide op l payload Z
  r ar eqn oldSites seen oneNode

private theorem bookedArchiveAtSeed {a R : ℕ} (hp : 0 < a) (sh : WorldShape a R ar.bit)
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
    (nr : DatePorts.OrderedSlotGeometry.ordering physicalGeometry) (ok : DatePorts.OrderedSlotGeometry.room physicalGeometry)
    {w : ℕ} (m : Memory w)
    (units : 1≤R) (widths : ∀ y,a∣bits y) {final z' D' : ℕ} {Last : MarkedWorld F d P bits}
    (target : Reached Last G q fee S k final z' D' wire l.seedWidth)
    (path : Path (SeedNamed.transport r eqn) target) (floor : ℕ)
    (paid : DatePorts.SeedArchiveAssembly.result (DatePorts.physicalReadAssembly (choice:=choice) G X digits publicWide op menu l payload Z r ar eqn
      oldSites seen oneNode hp sh inputPin oldRaw sameSite counted pointers wide pieces previous code oldLabel nr ok m)) :
    rawFirst r ar eqn hp units widths sh op menu code inputPin nr target path ⟨physicalPorts,floor⟩ m :=
  rawClaimHere r ar eqn hp units widths sh op menu code inputPin nr target path ⟨physicalPorts,floor⟩ m ok paid


private theorem purchasedNamedSeed {a R : ℕ} (hp : 0 < a) (sh : WorldShape a R ar.bit)
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
    {w : ℕ} (m : Memory w)
    (units : 1 ≤ R) (widths : ∀ y, a ∣ bits y) {final z' D' : ℕ} {Last : MarkedWorld F d P bits}
    (target : Reached Last G q fee S k final z' D' wire l.seedWidth)
    (path : Path (SeedNamed.transport r eqn) target) (floor : ℕ)
    (dst : Archive W') (shapeDst : WorldShape a R dst.bit)
    (codeDst : Encoding (Label G l.seedWidth Z op) (dictionary G op menu a) dst.bit)
    (sameAr : (transportArchive (renamedArchive ar (site r) (edge r)) eqn).data = dst)
    (sameSh : HEq ((transportArchive (renamedArchive ar (site r) (edge r)) eqn).carry
      (fun _ b => WorldShape a R b.bit) (sh.renamed (site r) (edge r))) shapeDst)
    (sameCode : HEq (Palette.transported r ar eqn code) codeDst)
    (number : Local dst.bit) (room : DatePorts.RangeRoom physicalPorts (SeedNamed.transport r eqn) dst.bit)
    (records : ∀ (nr : DatePorts.OrderedSlotGeometry.ordering physicalGeometry) (ok : DatePorts.OrderedSlotGeometry.room physicalGeometry),
      DatePorts.SeedArchiveAssembly.result (DatePorts.physicalReadAssembly (choice:=choice) G X digits publicWide op menu l payload Z r ar eqn
          oldSites seen oneNode hp sh inputPin oldRaw sameSite counted pointers wide pieces previous code oldLabel nr ok m)) :
    claimOnPath (SeedNamed.transport r eqn) target path hp units widths op menu dst number shapeDst codeDst
      inputPin Path.here ⟨physicalPorts, floor⟩ m := by
  refine nameFirstArchive r ar eqn hp units widths sh op menu code inputPin target path dst sameAr shapeDst codeDst sameSh sameCode
    number ⟨physicalPorts,floor⟩ m room ?_
  intro nr ok
  exact bookedArchiveAtSeed G X digits publicWide op menu l payload Z r ar eqn oldSites seen oneNode hp sh inputPin oldRaw sameSite counted pointers wide pieces previous code oldLabel nr ok m units widths target path floor (records nr ok)

private theorem purchasedAcrossWorlds {a R : ℕ} (hp : 0 < a) (sh : WorldShape a R ar.bit)
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
    {w : ℕ} (m : Memory w)
    (units : 1 ≤ R) (widths : ∀ y, a ∣ bits y) {final z' D' : ℕ} {Last : MarkedWorld F d P bits}
    (target : Reached Last G q fee S k final z' D' wire l.seedWidth)
    (namedLink : world r = W')
    (namedWorld : MarkedWorld F d P bits)
    (namedSource : Reached namedWorld G q fee S k 0 Z 3 wire l.seedWidth)
    (eqWorld : W' = namedWorld) (sameSource : HEq (SeedNamed.transport r namedLink) namedSource)
    (path : Path namedSource target) (floor : ℕ)
    (dst : Archive namedWorld) (shapeDst : WorldShape a R dst.bit)
    (codeDst : Encoding (Label G l.seedWidth Z op) (dictionary G op menu a) dst.bit)
    (sameAr : HEq (transportArchive (renamedArchive ar (site r) (edge r)) namedLink).data dst)
    (sameSh : HEq ((transportArchive (renamedArchive ar (site r) (edge r)) namedLink).carry
      (fun _ b => WorldShape a R b.bit) (sh.renamed (site r) (edge r))) shapeDst)
    (sameCode : HEq (Palette.transported r ar namedLink code) codeDst)
    (number : Local dst.bit) (room : DatePorts.RangeRoom physicalPorts namedSource dst.bit)
    (records : ∀ (nr : DatePorts.OrderedSlotGeometry.ordering physicalGeometry) (ok : DatePorts.OrderedSlotGeometry.room physicalGeometry),
      DatePorts.SeedArchiveAssembly.result (DatePorts.physicalReadAssembly (choice:=choice) G X digits publicWide op menu l payload Z r ar eqn
          oldSites seen oneNode hp sh inputPin oldRaw sameSite counted pointers wide pieces previous code oldLabel nr ok m)) :
    claimOnPath namedSource target path hp units widths op menu dst number shapeDst codeDst
      inputPin Path.here ⟨physicalPorts, floor⟩ m := by
  have links : namedLink = eqn := Subsingleton.elim _ _
  subst namedLink
  subst namedWorld
  obtain rfl := eq_of_heq sameSource
  exact purchasedNamedSeed G X digits publicWide op menu l payload Z r ar eqn oldSites seen oneNode hp sh inputPin
    oldRaw sameSite counted pointers wide pieces previous code oldLabel m units widths target path floor dst shapeDst codeDst
    (eq_of_heq sameAr) sameSh sameCode number room records

end PhysicalBooking
open private Palette.renameEncoding Palette.carryEncoding from OAI.Hierarchy.DescentNamedPrimitivePalette
open private transportArchive from OAI.Hierarchy.DescentNamedOriginalArchive
open DescentKernelHistory DescentBundleHistory
section
variable {F P : Type} [_root_.Field F] {bits : P → ℕ} {d : ℕ} {W W' : MarkedWorld F d P bits}
    {D : PoweredGadget F} {q fee : ℝ} {S : AtomSchedule} {k z wire s : ℕ}
    {U : Type} {dict : U → List (List Bool) → F}
private theorem seededCodeAtTransport (r : Reached W D q fee S k 0 z 3 wire s) (ar : Archive W)
    (same : world r = W') (code : Encoding U dict ar.bit) :
    HEq (Palette.transported r ar same code)
      (Palette.carryEncoding (transportArchive (renamedArchive ar (site r) (edge r)) same)
        (Palette.renameEncoding ar (site r) (edge r) code)) := by
  cases same
  rfl
end

open private Palette.shape_carry Palette.outputShape Palette.placedCode Palette.package_identity
  from OAI.Hierarchy.DescentNamedTerminalSliceLayout
open private Origin.archive_eq changeShapeArchive from OAI.Hierarchy.DescentNamedHistoryShape
open private Palette.changeEncoding from OAI.Hierarchy.DescentNamedPrimitivePalette
open private renamedShape Origin.originalShape Origin.physicalShape from OAI.Hierarchy.DescentNamedSeedInitialShape
section
variable {F P : Type} [_root_.Field F] {bits : P→ℕ} {d : ℕ} {V : MarkedWorld F d P bits}
private theorem samePackageShape {U : MarkedWorld F d P bits} {a : Archive U}
    (src dst : ArchiveTransport a V) (e : src = dst) {p R : ℕ}
    (shape : WorldShape p R a.bit) :
    HEq (src.carry (fun _ b=>WorldShape p R b.bit) shape) (dst.carry (fun _ b=>WorldShape p R b.bit) shape) := by
  cases e
  rfl
private theorem samePackageCode {U : MarkedWorld F d P bits} {a : Archive U} {K : Type} {dict : K→List (List Bool)→F}
    (src dst : ArchiveTransport a V) (e : src=dst) (code : Encoding K dict a.bit) :
    HEq (Palette.carryEncoding src code) (Palette.carryEncoding dst code) := by
  cases e
  rfl
private theorem changedShapeEq (a b : Archive V) (same : a=b) {p R : ℕ} (sh : WorldShape p R a.bit) :
    HEq sh (changeShapeArchive a b same p R sh) := by
  cases same
  rfl
private theorem changedCodeEq {U : Type} {dict : U→List (List Bool)→F}
    (a b : Archive V) (same : a=b) (e : Encoding U dict a.bit) :
    HEq e (Palette.changeEncoding a b same e) := by
  cases same
  rfl
end

section
attribute [local irreducible] Origin.archivePackage Origin.source
variable {F : Type} [Field F] {cp pins : ℕ} {X : Approximation F cp pins} {D : PoweredGadget F}
    {S : AtomSchedule} {q fee : ℝ} {k s z wire p R : ℕ}
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
    (o : Origin (G:=D) (S:=S) (s:=s) (q:=q) (fee:=fee) (z:=z) (wire:=wire) X c digits)
    (hp : 0<p) (one : 1≤R) (divides : p∣s) (op : RotorSpec) (menu : Runnable F op)
set_option quotPrecheck false
local notation "packSeed" => transportArchive (renamedArchive (seedArchive X S.copies s c) (site o.raw) (edge o.raw)) (linked_world X c digits o.seed)
local notation "rawShape" => (seedRetained X S.copies s hp one divides c).shape
local notation "rawCode" => DescentPrimitivePalette.seeded (G:=D) (Z:=z) (p:=p) op menu X c
private theorem seedArchivesIdentical : (packSeed).data = o.archive :=
  (congrArg ArchiveTransport.data (Palette.package_identity o).symm).trans (Origin.archive_eq o).symm
private theorem seedShapesIdentical :
    HEq ((packSeed).carry (fun _ b=>WorldShape p R b.bit) (Origin.physicalShape o p R hp one divides))
      (Origin.archiveShape o p R hp one divides) := by
  have carried := Palette.shape_carry o hp one divides
  have steps := changedShapeEq o.archivePackage.data o.archive (Origin.archive_eq o).symm (Palette.outputShape o hp one divides)
  have moved := samePackageShape packSeed o.archivePackage (Palette.package_identity o).symm (Origin.physicalShape o p R hp one divides)
  have finalStep := (heq_of_eq carried.symm).trans steps
  have together := moved.trans finalStep
  change HEq _ (changeShapeArchive o.archivePackage.data o.archive (Origin.archive_eq o).symm p R (Palette.outputShape o hp one divides))
  exact together
private theorem rawRetainedShape :
    Origin.physicalShape o p R hp one divides =
      WorldShape.renamed (B := (seedArchive X S.copies s c).bit) rawShape (site o.raw) (edge o.raw) := by
  unfold Origin.physicalShape renamedShape Origin.originalShape
  rfl

private theorem seedShapesWithRawData :
    HEq ((packSeed).carry (fun _ b=>WorldShape p R b.bit)
      (WorldShape.renamed (B := (seedArchive X S.copies s c).bit) rawShape (site o.raw) (edge o.raw)))
      (Origin.archiveShape o p R hp one divides) := by
  have atRaw := congrArg ((packSeed).carry (fun _ b=>WorldShape p R b.bit)) (rawRetainedShape o hp one divides).symm
  exact (heq_of_eq atRaw).trans (seedShapesIdentical o hp one divides)

private theorem seedCodesIdentical :
    HEq (Palette.transported o.raw (seedArchive X S.copies s c) (linked_world X c digits o.seed) rawCode)
      (Palette.encodedOrigin (p:=p) o op menu) := by
  have placed := seededCodeAtTransport o.raw (seedArchive X S.copies s c) (linked_world X c digits o.seed) rawCode
  have changed := changedCodeEq o.archivePackage.data o.archive (Origin.archive_eq o).symm
    (Palette.carryEncoding o.archivePackage (Palette.placedCode (p:=p) o op menu))
  have moved := samePackageCode packSeed o.archivePackage (Palette.package_identity o).symm (Palette.placedCode (p:=p) o op menu)
  unfold Palette.encodedOrigin
  exact placed.trans (moved.trans changed)
private theorem initialStateEq :
    initial_world X S.copies s (S.groupCount 0) k digits c =
    (initial X S.copies s (S.groupCount 0) k digits).state c := rfl
private theorem linkedSourceEq :
    HEq (SeedNamed.transport o.raw (linked_world X c digits o.seed)) o.source := by
  unfold Origin.source
  rfl
private theorem physicalArchiveHEq :
    HEq (packSeed).data o.archive := by
  exact heq_of_eq (seedArchivesIdentical o)
end

open private DatePorts.seedReadAssembly DatePorts.SeedArchiveAssembly.result DatePorts.physicalReadAssembly from OAI.Hierarchy.DescentSeedCompleteArchive
open private DatePorts.originalGeometry DatePorts.OrderedSlotGeometry.ordering DatePorts.OrderedSlotGeometry.room from OAI.Hierarchy.DescentDatedSeedSlotGeometry
private theorem seedPinWidths (I : Type) (a s : ℕ) (divides : a ∣ s) : ∀ _ : I, a ∣ s*1 := by
  intro _
  simpa only [Nat.mul_one] using divides

open Lean Elab Term in
local elab "seedBankRead" : term => do
  let mut proof := Lean.mkConst ``issued_startup_archive
  let mut ty := (← Lean.getConstInfo ``issued_startup_archive).type
  while let .forallE name dom body binder := ty do
    let arg ← if binder.isInstImplicit then Lean.Meta.synthInstance dom else Lean.Meta.getFVarFromUserName name
    proof := Lean.mkApp proof arg
    ty := body.instantiate1 arg
  let some projected ← Lean.Meta.withTransparency .all (Lean.Meta.whnfUntil ty ``DatePorts.SeedArchiveAssembly.result)
    | throwError "expected the original seed bank result"
  let some oldAssembly := projected.getAppArgs.back? | throwError "empty seed projection"
  let some paidAssembly ← Lean.Meta.delta? oldAssembly.consumeMData (· == ``DatePorts.seedReadAssembly)
    | throwError "expected a physical seed assembly"
  let readProp := Lean.mkApp (Lean.mkConst ``DatePorts.SeedArchiveAssembly.result) paidAssembly
  return Lean.mkApp2 (Lean.mkConst ``id [.zero]) readProp proof

variable {F P : Type} [Field F] {S : AtomSchedule} (D : PoweredGadget F) (op : RotorSpec)
  {k cp p H e j r t w : ℕ} (X : Approximation F cp p) (radix : S.radix=2^k)
  (publicWide : Fintype.card (Vertex X) ≤ H) (l : Layout) (header payload Z : ℕ)
  (seed : Select X S.copies l.seedWidth → P) (lo C grain : ℕ) (ss : List (Source P)) (origin extra : ℕ)
  (ex : Fin e → Plane j r → Fin t → Bool) (z : P⊕Hidden e j r t → Bool) (back : Memory w)
local notation "G" => S.groupCount 0
local notation "digits" => S.initialDigits radix
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage Origin.archiveShape Palette.encodedOrigin
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => endAddress X l H G k
local notation "chart" => nodeChart l k H G
local notation "finish" => (chart).seedEnd top
local notation "lowEnd" => end_ (lo+extent grain ss) C grain
local notation "front" => origin+17*DescentExteriorShelf.span j r t e
local notation "raw" => Root.appended front extra (Root.widePackedImage X S.copies l.seedWidth payload w seed lo C grain ss origin ex z) back
local notation "counted" => DescentWideSeedFlags.countedAt X S.copies l.seedWidth payload seed (z∘Sum.inl) raw
local notation "flag" => DescentWideSeedFlags.endInput X S.copies l.seedWidth payload
local notation "entries" => DescentPackedSeed.rows X S.copies l.seedWidth payload
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "lanes" => Primitive.paletteLanes D op l.seedWidth Z payload k
local notation "cap" => Primitive.initialEnd X S.copies l.seedWidth payload k H G lanes finish
local notation "done" => completeImage D op X digits publicWide l header payload Z counted
variable {q ε : ℝ} {wire : ℕ} {c : (initialGroup X S.copies l.seedWidth).Choice}
  (o : Origin X (s:=l.seedWidth) («G»:=D) (S:=S) (q:=q) (fee:=ε) (z:=Z) (wire:=wire) c (S.initialDigits radix))
  (wide : Fintype.card o.raw.V ≤ H)


local notation "ports" => DatePorts.initial D op X S.copies l k H G payload Z
variable (menu : Runnable F op) (number : Local o.archive.bit)
  (register : DatePorts.RangeRoom (DatePorts.initial D op X S.copies l k H (S.groupCount 0) payload Z)
    o.source o.archive.bit)
  {a R : ℕ} (hp : 0<a) (units : 1≤R) (whole : a∣l.seedWidth)
local notation "shape_" => Origin.archiveShape o a R hp units whole
local notation "label" => (Palette.encodedOrigin (p:=a) o op menu).atNode
local notation "names" => Reached.argumentPointer o.source o.archive.bit number shape_ hp
  (fun y : (Σ _ : Fin S.copies,Fin (Fintype.card (Port p X.width)))=>y.1.val) (ports).argumentsPerNode

local notation "pins" => Σ _ : Fin S.copies,Fin (Fintype.card (Port p X.width))
variable {epoch z' degree':ℕ}
  {targetWorld : MarkedWorld F 0 (Σ _ : Fin S.copies, Fin (Fintype.card (Port p X.width))) (fun _=>l.seedWidth*1)}
  (target:Reached targetWorld D q ε S k epoch z' degree' wire l.seedWidth) (path:Path o.source target)
local notation "trace" => (⟨(initial X S.copies l.seedWidth (S.groupCount 0) k digits).state c, targetWorld, Z, 3, z', degree', o.source, target, path⟩:
  RunTrace D q ε S k wire l.seedWidth epoch (fun _ : pins=>l.seedWidth*1) 0)
local notation "pos₀" => (⟨ports,cap⟩:RegisterTimeline.Position)
local notation "pinWidth" => (fun _ : pins=>by simpa only [Nat.mul_one] using whole)
include menu number hp units whole in
def issuedSeedArchiveClaim : PrefixClaim trace w :=
  claimOnPath o.source target path hp units pinWidth op menu o.archive number
    (Origin.archiveShape o a R hp units whole) (Palette.encodedOrigin (p:=a) o op menu) (fun y:pins=>y.1.val)

def issuedSeedClaimAtFirst (pos : RegisterTimeline.Position) (mem : Memory w) : Prop :=
  atFirstRegister trace (issuedSeedArchiveClaim (w:=w) D op X radix l Z o menu number hp units whole target path) pos mem

local notation "actual" => issuedSeedArchiveClaim (w:=w) D op X radix l Z o menu number hp units whole target path


include wide register in
set_option maxHeartbeats 300000 in
theorem issued_startup_register {cw : ℕ} (width : 16*digitsNeeded l.seedWidth ≤ payload)
    (live : 0 < lanes) (machine : payload ≤ w) (bits : DescentPrimitivePalette.printedBits D l.seedWidth Z op*lanes ≤ w)
    (fit : l.seedWidth < 2^cw) (decoded : decode X ((z∘Sum.inl)∘seed)=some c)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w) (fieldRoom : l.operandBits*l.operandLanes ≤ w)
    (seedFits : flag+(entries+1) < 2^w) (seedBefore : flag+(entries+1) ≤ lo)
    (shelves : lowEnd ≤ origin) (privateAfter : front+extra ≤ header) (early : header < l.base) (space : cap < 2^w)
    (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish)
    (wordRoom : 3<2^l.operandBits) (copies : S.copies≤2^l.operandBits) (quota : l.groupsPerNode≤2^l.operandBits)
    (pieces : l.groupsPerNode=l.seedWidth/a) :
    (ports).held o.source cap done ∧ actual (show Path o.source o.source from .here) pos₀ done:=by
  refine ⟨initial_held D op X digits publicWide l header payload Z o wide counted signed fieldRoom early
    sourceSpace live machine space,?_⟩
  let readAll := fun
    (number : DatePorts.OrderedSlotGeometry.ordering (DatePorts.originalGeometry X (S.initialDigits radix) publicWide op l payload Z o))
    (register : DatePorts.OrderedSlotGeometry.room (DatePorts.originalGeometry X (S.initialDigits radix) publicWide op l payload Z o)) =>
    seedBankRead
  have sameAr := seedArchivesIdentical o
  have eqWorld := initialStateEq (X:=X) (S:=S) (s:=l.seedWidth) (k:=k) («digits»:=S.initialDigits radix) (c:=c)
  have refSource := linkedSourceEq o
  have commonAr := physicalArchiveHEq o
  have sameSh := seedShapesWithRawData o hp units whole
  have sameCode := seedCodesIdentical (p:=a) o op menu
  have shardWidths := seedPinWidths pins a l.seedWidth whole
  let floorSeed := cap
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let records ← Lean.Meta.getFVarFromUserName `readAll
      let outerNumber ← Lean.Meta.getFVarFromUserName `number
      let outerRoom ← Lean.Meta.getFVarFromUserName `register
      let recordType ← Lean.Meta.inferType records
      Lean.Meta.forallBoundedTelescope recordType (some 2) fun _ assemblyType => do
        let some projected ← Lean.Meta.withTransparency .all (Lean.Meta.whnfUntil assemblyType ``DatePorts.SeedArchiveAssembly.result)
          | throwError "expected the physical seed archive on this register"
        let some assembly := projected.getAppArgs.back? | throwError "empty seed assembly projection"
        let some underlying ← (if assembly.getAppFn.isConstOf ``DatePorts.physicalReadAssembly then pure (some assembly) else Lean.Meta.delta? assembly.consumeMData (· == ``DatePorts.seedReadAssembly))
          | throwError "expected the seed-world specialization"
        let underlying := underlying.consumeMData
        unless underlying.getAppFn.isConstOf ``DatePorts.physicalReadAssembly do throwError "expected the physical seed reader"
        let mut inputs : Lean.NameMap Lean.Expr := {}
        let mut formals := (← Lean.getConstInfo ``DatePorts.physicalReadAssembly).type
        for arg in underlying.getAppArgs do
          let .forallE name _ body _ := formals | throwError "unexpected physical reader telescope"
          inputs := inputs.insert name arg
          formals := body.instantiate1 arg
        inputs := (inputs.insert `number outerNumber).insert `room outerRoom
        for (dst,equality) in #[(`dst,`sameAr),(`shapeDst,`sameSh),(`codeDst,`sameCode)] do
          let h ← Lean.Meta.getFVarFromUserName equality
          let ht ← Lean.instantiateMVars (← Lean.Meta.inferType h)
          let eqName := if equality == `sameAr then ``Eq else ``HEq
          let some eqType ← Lean.Meta.withTransparency .all (Lean.Meta.whnfUntil ht eqName)
            | throwError "expected seed field agreement {equality}"
          let some value := eqType.getAppArgs.back? | throwError "empty equality {equality}"
          inputs := inputs.insert dst value
          if equality == `sameAr then
            let lhs := eqType.getAppArgs[1]!
            let some pkg := lhs.getAppArgs.back? | throwError "expected the transported seed archive"
            let some worldProof := pkg.getAppArgs.back? | throwError "expected the seed world's equality proof"
            inputs := inputs.insert `namedLink worldProof
        let worldEq ← Lean.Meta.getFVarFromUserName `eqWorld
        let srcEq ← Lean.Meta.getFVarFromUserName `refSource
        let some wTy ← Lean.Meta.withTransparency .all (Lean.Meta.whnfUntil (← Lean.Meta.inferType worldEq) ``Eq)
          | throwError "expected the selected initial state"
        let some sTy ← Lean.Meta.withTransparency .all (Lean.Meta.whnfUntil (← Lean.Meta.inferType srcEq) ``HEq)
          | throwError "expected the selected initial source"
        inputs := (inputs.insert `namedWorld wTy.getAppArgs.back!).insert `namedSource sTy.getAppArgs.back!
        inputs := (inputs.insert `eqWorld worldEq).insert `sameSource srcEq
        inputs := inputs.insert `sameAr (← Lean.Meta.getFVarFromUserName `commonAr)
        let mut applied := Lean.mkConst ``purchasedAcrossWorlds
        let mut ty := (← Lean.getConstInfo ``purchasedAcrossWorlds).type
        while let .forallE nm dom rest kind := ty do
          let arg ← if let some value := inputs.find? nm then pure value
            else if kind.isInstImplicit then Lean.Meta.synthInstance dom
            else Lean.Meta.getFVarFromUserName (match nm with
              | `Last => `targetWorld | `final => `epoch | `D' => `degree' | `widths => `shardWidths
              | `floor => `floorSeed | `records => `readAll | `room => `register | a => a)
          applied := Lean.mkApp applied arg
          ty := rest.instantiate1 arg
        g.assign applied

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
