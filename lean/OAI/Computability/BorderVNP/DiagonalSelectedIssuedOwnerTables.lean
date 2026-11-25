import OAI.Computability.BorderVNP.DiagonalPinnedRouteObservation
import OAI.Computability.BorderVNP.DiagonalSelectedPreCallSources
import OAI.Computability.BorderVNP.DiagonalDecodedOwnerTables

/-! # Actual report owners and owner tables in the frozen all-team prefix decoder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open BorderVNP.Cube Physical Physical.NativeAssignments DiagonalTallyCellReports ReportDirectory
variable {R bundles : ℕ} (ar : CubeArena.Layout)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (label : Fin ar.cells → Label (ar.n+1) ar.header.d)
    (charts : Fin (R+1) → ReportLayout) (home : Fin bundles → Fin ar.cells) (bodies : Fin bundles → ReportBundle)
    (supplied wires : ℕ → ℕ) (q : Routed (b:=ar.b) (s:=ar.s) owners)

/-- The team attached to a compact ordinal is the actual owner of its routed global cell. -/
theorem routedReceivedRows_owner (u : Fin (R+1))
    (i : Fin ((routedReceivedRows ar owners label charts home bodies supplied wires q).cells u).length) :
    owners q.1 (label ((routedReceivedRows ar owners label charts home bodies supplied wires q).order ⟨u,i⟩)
      (chosen ar.b ar.s q.1))=u :=
  receivedSourceRows_owner charts home bodies (fun c => owners q.1 (label c (chosen ar.b ar.s q.1)))
    (routedOwnerWord ar owners label q) (routedOwnerWord_at ar owners label q)
    (fun c => ar.cellBank+c*ar.cellStride) supplied wires (fun _ _ _ _ => false) u i

end RoutingISA.Evaluator.SignedPrep

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.CellEntries
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP
open VPVNP.ParseGrammar EnrichedOuter TeamScales BorderVNP.Cube.Physical.NativeAssignments
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 3200000
set_option maxRecDepth 7200
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r pins link k d a regs rw ec width s copies T header work : ℕ}
    (plan : SeedPlan S (k+1) r d T copies header work)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
local notation3 (prettyPrint := false) "axes" => Fintype.card (Cube D)
local notation3 (prettyPrint := false) "tiles" => GridHosts.tileCount (Fintype.card (Cube D)) d
local notation3 (prettyPrint := false) "G₀" => tapeTemplate p fit pins
variable {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : PairedParameters k s ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate p fit pins)) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)
local notation3 (prettyPrint := false) "C" => plan.compiled
local notation3 (prettyPrint := false) "mass" => initialMass (D:=D) (k+1) r d copies header
local notation3 (prettyPrint := false) "budget" => boundaryBudget S mass
local notation3 (prettyPrint := false) "word₀" => 60*logWidth r (k+1)
local notation3 (prettyPrint := false) "seedBlock" => GridHosts.inputBlockWidth r (k+1) axes d
local notation3 (prettyPrint := false) "seedCap" => seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))
local notation3 (prettyPrint := false) "desc" => seedDescriptionWidth (k+1) r axes d (header*logWidth r (k+1)) (BottomGridBank.bodyBudget seedCap)

variable (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*logWidth r (k+1)) 0 → Bool)
    (good : Boundary.Good (boundaryBudget S (initialMass (D:=D) (k+1) r d copies header)) 0 (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
    (y : e.Entry → E) (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)
local notation3 (prettyPrint := false) "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := word₀) budget
local notation3 (prettyPrint := false) "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation3 (prettyPrint := false) "baseProg" => Boundary.wiredSeedStatePrograms S W position code sites edges ports copies table words
local notation3 (prettyPrint := false) "source" => EnrichedTape.base (Gadget := Gadget) p fit W position leaf rfl
local notation3 (prettyPrint := false) "key" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation3 (prettyPrint := false) "M" => (C).machine
local notation3 (prettyPrint := false) "rows" => (C).privateSiteRows key seeds
local notation3 (prettyPrint := false) "oldPorts" => privatePorts S key
local notation3 (prettyPrint := false) "G₁" => SewnTape.wiring p fit free pins
variable (hp : (fieldSewParams (SewnTape.wiring p fit free pins) (Fintype.card (Cube D)) d).Valid)
open BorderVNP.Cube (TableEntry)
open BorderVNP.Cube.Physical Packing.CellAddresses Packing.BottomReports
open BorderVNP.Packing.RoutingOutputs.NativeDemands
open RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open DiagonalTallyAllocation DiagonalTallyCellReports ReportDirectory

variable {F : Type} [Field F] (cube : FixedCube F) (α ξ : ℝ)
    (calibrated : plan.SignedLabelRows count link (cube.pred+1) α ξ)
    (lit : (UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a) = literal α (k+1))
    (hd : 0 < BorderVNP.Cube.alphabet α (k+1)) {cells : ℕ}
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells)

variable (parameters : RoutingISA.SignedTaskArena.Parameters)
local notation3 (prettyPrint := false) "gap" => parameters.privateGap
local notation3 (prettyPrint := false) "deliveries" => freeDirectory R r ((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))
  link tiles seedBlock ((fan S)^T*tiles) desc
variable (arenaBase profileBits : ℕ)
local notation3 (prettyPrint := false) "arena" =>
  (CubeArena.selectedSizes arenaBase (BorderVNP.Cube.alphabet α (k+1)) ((R+1)*exterior ξ r (k+1))
    cells ((boundary S (d+1) T).edges+4*((R+1)*CoverScale.sites (Cube D) (d+1))) (deliveries).candidates
    (R+1) r (k+1) profileBits).selected cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "task" => (SignedTaskArena.Layout.mk arena (cube.cubeID e) parameters)
variable (frame origin : Fin (R+1) → ℕ)
local notation3 (prettyPrint := false) "charts" => fun u : Fin (R+1) =>
  reportLayout (task).before (task).after (frame u)
    (RoutingOutputs.controlsBase (origin u) (arena).cables cells (deliveries).entries ((R+1)*tiles))
    parameters.parameters parameters.siteWidth parameters.bodyCap (arena).stop

open VPVNP.BurstRAM TeamContraction.ProcessorSlots Routing CellMacro.Generator RoutingISA.CompactMachine
local notation3 (prettyPrint := false) "Hist" => (packHistory leaf plan.compiled.machine.epoch T).Index
local notation3 (prettyPrint := false) "core(" h ")" => plan.signedCoreDirectory (R := R) (r := r) (pins := pins) (link := link) (k := k) (d := d) (a := a) (regs := regs) (rw := rw) (ec := ec) (width := width) (s := s) (copies := copies) (T := T) (header := header) (work := work) p fit W position code
  sites edges ports table words good seeds free count pos num hp h cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "rsrc(" h ")" => plan.signedReportSources (R := R) (r := r) (pins := pins) (link := link) (k := k) (d := d) (a := a) (regs := regs) (rw := rw) (ec := ec) (width := width) (s := s) (copies := copies) (T := T) (header := header) (work := work) p fit W position code
  sites edges ports table words good seeds free count pos num hp h cube α ξ calibrated lit hd number parameters
  arenaBase profileBits frame origin
local notation3 (prettyPrint := false) "recv(" h "," v ")" => plan.signedReceivedRows (R := R) (r := r) (pins := pins) (link := link) (k := k) (d := d) (a := a) (regs := regs) (rw := rw) (ec := ec) (width := width) (s := s) (copies := copies) (T := T) (header := header) (work := work) p fit W position code
  sites edges ports table words good seeds free count pos num hp h cube α ξ calibrated lit hd number parameters
  arenaBase profileBits frame origin v
local notation3 (prettyPrint := false) "routes" => fun h : Hist => (core(h)).Route cube.width
local notation3 (prettyPrint := false) "proposals" => fun (_ : Fin pins → Bool) (h : Hist) (v : (core(h)).Route cube.width) =>
  (u : Fin (R+1)) → ReportAssignments ((recv(h,v.val)).cells u)

local notation3 (prettyPrint := false) "packet(" h ")" => plan.signedPackets count G₀ order position W code sites edges ports table
  words good cube α ξ calibrated lit hd hp number gap h

/-- Each global cell of the selected signed history is processed by the real packet's greedy
group at the axis selected by that route. -/
noncomputable def signedIssuedOwner (h : Hist) (v : (core(h)).Route cube.width) (c : Fin (core(h)).cells) : Fin (R+1) :=
  (core(h)).owners v.val.1 ((packet(h)).label c (BorderVNP.Cube.Physical.chosen cube.b cube.width v.val.1))

local notation3 (prettyPrint := false) "who" => plan.signedIssuedOwner (R:=R) (r:=r) (pins:=pins) (link:=link)
  (k:=k) (d:=d) (a:=a) (regs:=regs) (rw:=rw) (ec:=ec) (width:=width) (s:=s) (copies:=copies) (T:=T)
  (header:=header) (work:=work) p fit W position code sites edges ports table words good seeds free count pos num hp
  cube α ξ calibrated lit hd number parameters

/-- Every compact reported ordinal belongs to its own selected physical team. -/
theorem signedIssuedOwner_order (h : Hist) (v : (core(h)).Route cube.width) (u : Fin (R+1))
    (i : Fin ((recv(h,v.val)).cells u).length) :
    who h v ((recv(h,v.val)).order ⟨u,i⟩)=u := by
  unfold signedIssuedOwner signedReceivedRows
  exact routedReceivedRows_owner arena (core(h)).owners (packet(h)).label _ _ _ _ _ v.val u i

variable {clockWidth headerCap tallyWidth columns : ℕ} (pub : Fin (R+1) → Arg → Word clockWidth)
    (reg : Fin (R+1) → Bank clockWidth) (args : Fin (R+1) → UnitAddresses) (readerPin : Fin pins → Bool)
    (layout : WireLayout (R+1) r link) (fixed : Block (R+1)) (hw : 0<clockWidth)
    (agreeWidth : ∀ u, (args u).header = layout.header) (base : Fin (R+1) → ℕ)
local notation3 (prettyPrint := false) "headers" => JointHeader.PositiveFields.width profileBits cube.pred
  (BorderVNP.Cube.alphabet α (k+1)) headerCap (R+1) columns tallyWidth
local notation3 (prettyPrint := false) "claims" => Fin ((R+1)*columns*tallyWidth) → Bool
local notation3 (prettyPrint := false) "domains" => PreparedFields (Fin pins → Bool) Hist claims routes proposals

/-- Apply the owner table built at every true signed physical launch to the exact dependent
inverse of the issued prefix decoder. The owner and the number of global cells are selected by
the real geometry history; the physical call table starts at the before-arena limit. -/
theorem signedSupportedIssuedOwnerTables (hdr : layout.header=headers)
    (room : ∀ u, ((G₁).transferFrame u (args u).header (args u).dst).Fits clockWidth (base u))
    (enc : Hist ↪ (Fin profileBits → Bool))
    (B₀ : (z : {ext // PositiveExterior G₁ args readerPin clockWidth ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G₁ pub reg args readerPin z.val u)
    (decoder : BootedPinStart.PreparedHistoryDecoder SparseExterior.driver (cube.cubeID e) G₁ pub reg
      readerPin layout hdr enc args fixed hw agreeWidth base room B₀) :
    let U := fun z u => (B₀ z u).start
    let ib := fun u => (args u).ibase
    let hb := fun u => (args u).hbase
    let sb := fun u => (args u).starbase
    let mac := TeamSiteEvents.macros (w := clockWidth) (siteLibrary SparseExterior.driver) (nativeClock (k+1))
    ∀ (limit burst : ℕ) (privateRoom : TeamScales.width (k+1) (1/2) ≤ burst)
      (next : ∀ (z : {ext // PositiveExterior G₁ args readerPin clockWidth ext ∧ PinStart.preCallSupport U (cube.cubeID e) ext})
        (u : Fin (R+1)), let team := B₀ ⟨z.val,z.property.1⟩ u
        PositiveContinuation (cube.cubeID e) SparseExterior.driver (k+1) (pub u) mac team.start.bank team.memory team.pins team.used limit)
      (routed : ∀ i (q : Hist) (claim : claims),
      (Σ c : Broadcast cube.pred (BorderVNP.Cube.alphabet α (k+1)) headerCap,
        ParsedPreCall G₁ args readerPin layout fixed hw agreeWidth base room hdr U ib hb sb (fun _ _ => rfl)
          (cube.cubeID e) i ⟨enc q,c,claim⟩) ≃ Σ v : routes q, proposals i q v),
    (∀ i h (v : (core(h)).Route cube.width) claim (r₀ : proposals i h v) (u : Fin (R+1)),
      let z := (routed i h claim).symm ⟨v,r₀⟩
      RoutingISA.CellDispatch.OwnerTable (pub u) (z.2.2 u).val.2.2 ⟨u.val,(task).before.limit,(core(h)).cells⟩
        (PositiveTeam.ownerWord (who h v))) →
    let team := BootedPinStart.supportedTeam (cube.cubeID e) B₀ limit burst privateRoom next
    let prep := (decoder.supported limit burst privateRoom next routes proposals routed).val
    ∀ (f : domains) (u : Fin (R+1)),
      let z := prep.symm f
      RoutingISA.CellDispatch.OwnerTable (team z.1 u).pub ((team z.1 u).postMemory (z.2 u))
        ⟨u.val,(task).before.limit,(core(f.2.1)).cells⟩ (PositiveTeam.ownerWord (who f.2.1 f.2.2.1)) := by
  intro U ib hb sb mac limit burst privateRoom next routed produced
  exact BootedPinStart.PreparedHistoryDecoder.supported_owner_tables SparseExterior.driver (cube.cubeID e) G₁
    pub reg readerPin layout hdr enc args fixed hw agreeWidth base room B₀ routed decoder limit burst privateRoom next
    (fun h : Hist => (core(h)).cells) who
    (fun (_ : domains) (_ : Fin (R+1)) => (task).before.limit) produced

local notation3 (prettyPrint := false) "nativeCap" =>
  declarationCap (arena).n (arena).header.d (arena).header.blocks (arena).b (arena).h (arena).s

/-- The exact issued source of the frozen boundary history recovers the physical writer,
complete owner handoff, and observed routed choice from the original all-team pinned prefix. -/
theorem signedAdmittedOwnerObservation
    (hdr : layout.header=JointHeader.PositiveFields.width profileBits cube.pred (BorderVNP.Cube.alphabet α (k+1))
      nativeCap (R+1) columns tallyWidth)
    (room : ∀ u, ((G₁).transferFrame u (args u).header (args u).dst).Fits clockWidth (base u))
    (enc : Hist ↪ (Fin profileBits → Bool))
    (B₀ : (x : {ext // PositiveExterior G₁ args readerPin clockWidth ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G₁ pub reg args readerPin x.val u)
    (i : Fin pins → Bool) (h : Hist) (claim : claims) (allowed : RawBroadcast arena → Prop)
    (template : DiagonalTallyPacketEmit.Frame) (entries : ℕ) :
    let U := fun z u => (B₀ z u).start
    let ib := fun u => (args u).ibase
    let hb := fun u => (args u).hbase
    let sb := fun u => (args u).starbase
    ∀ (candidates : AdmittedPinnedFrames G₁ args readerPin layout fixed hw agreeWidth base room arena hdr U ib hb sb
      (fun _ _ => rfl) (cube.cubeID e) (core(h)).owners (rsrc(h)) i (enc h) claim allowed template entries)
      (checked : ∀ c, ParsedPreCall G₁ args readerPin layout fixed hw agreeWidth base room hdr U ib hb sb
        (fun _ _ => rfl) (cube.cubeID e) i ⟨enc h,c,claim⟩ → LocalRow.declarationInRange c ∧ allowed c)
      (honest : ∀ a : BorderVNP.Cube.Physical.NativeAssignments.Routed (b:=cube.b) (s:=cube.width) (core(h)).owners,
        allowed (routeBroadcast arena (core(h)).owners a).val)
      (v : routes h) (r₀ : proposals i h v),
      let E := candidates.preparations G₁ args readerPin layout fixed hw agreeWidth base room arena hdr U ib hb sb
        (fun _ _ => rfl) (cube.cubeID e) (core(h)).owners (rsrc(h)) i (enc h) claim allowed template entries checked honest
      let c := routeBroadcast arena (core(h)).owners v.val
      let f := candidates.frame c (honest v.val)
      let dcl := decodedBroadcast arena c.val
      let declared : Declared arena (core(h)).owners dcl := ⟨v.val,(decoded_routeBroadcast arena (core(h)).owners v.val).symm⟩
      let raw := declaredWords arena (core(h)).owners dcl declared
      let selected : Matching arena (core(h)).owners dcl raw.val := ⟨v.val,declared.property,rfl⟩
      f.OwnedRouteOn fixed (cube.cubeID e) (core(h)).owners template entries raw selected
        (pinnedOwnedHistory G₁ args readerPin layout fixed hw agreeWidth base room arena hdr U ib hb sb
          (fun _ _ => rfl) (cube.cubeID e) i (enc h) claim (E.symm ⟨v,r₀⟩)) := by
  intro U ib hb sb candidates checked honest v r₀
  exact routedPinnedPreparations_observed G₁ args readerPin layout fixed hw agreeWidth base room arena hdr U ib hb sb
    (fun _ _ => rfl) (cube.cubeID e) (core(h)).owners (rsrc(h)) i (enc h) claim candidates.wire candidates.extent
    allowed checked honest candidates.frame candidates.builder candidates.source template entries candidates.observed v r₀

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
