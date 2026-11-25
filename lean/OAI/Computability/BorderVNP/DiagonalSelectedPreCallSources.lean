import OAI.Computability.BorderVNP.DiagonalAdmittedPinnedFrames
import OAI.Computability.BorderVNP.DiagonalSelectedReportRows
import OAI.Computability.BorderVNP.DiagonalRoutedCoreReadback
import OAI.Computability.BorderVNP.DiagonalBootedRouteDecoding

/-! # The bare and supported prefix decoder on the selected routed report cells -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep.SourceReports

open BorderVNP.Cube Physical Physical.NativeAssignments

/-- A shared routed source, its successful endpoint tests, and all the
independently chosen report paths before any team enters its cell bank. -/
abbrev Issued {R : ℕ} {ar : CubeArena.Layout}
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) →
      Fin ar.header.d → Fin (R+1)} (src : SourceReports ar owners) :=
  src.Proposals

end RoutingISA.Evaluator.SignedPrep.SourceReports

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

/-- The replayed route and the proposed reports in the stable geometric
directory are literally the issued route and per-team private claims of
this original history. Neither the raw pin nor any extra guesses are needed
to renumber the report slots. -/
noncomputable def signedIssuedPrefixCut (i : Fin pins → Bool) (q : Hist) (A : Type)
    (replay : A ≃ (rsrc(q)).Issued) :
    A ≃ Σ v : (core(q)).Route cube.width, proposals i q v := replay

variable {clockWidth headerCap tallyWidth columns : ℕ} (pub : Fin (R+1) → Arg → Word clockWidth)
    (reg : Fin (R+1) → Bank clockWidth) (args : Fin (R+1) → UnitAddresses) (readerPin : Fin pins → Bool)
    (layout : WireLayout (R+1) r link) (fixed : Block (R+1)) (hw : 0<clockWidth)
    (agreeWidth : ∀ u, (args u).header = layout.header) (base : Fin (R+1) → ℕ)
local notation3 (prettyPrint := false) "headers" => JointHeader.PositiveFields.width profileBits cube.pred
  (BorderVNP.Cube.alphabet α (k+1)) headerCap (R+1) columns tallyWidth
local notation3 (prettyPrint := false) "claims" => Fin ((R+1)*columns*tallyWidth) → Bool
local notation3 (prettyPrint := false) "domains" => PreparedFields (Fin pins → Bool) Hist claims routes proposals

/-- Select the concrete decoded fields from the frozen reader. The bare
certificate is available before any site continuation or joint clock.
The later supported decoder receives exactly that bare wire and RAM tuple. -/
noncomputable def signedBareIssuedPrefixes (hdr : layout.header=headers)
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
    ∀ (routed : ∀ i (q : Hist) (claim : claims),
      (Σ c : Broadcast cube.pred (BorderVNP.Cube.alphabet α (k+1)) headerCap,
        ParsedPreCall G₁ args readerPin layout fixed hw agreeWidth base room hdr U ib hb sb (fun _ _ => rfl)
          (cube.cubeID e) i ⟨enc q,c,claim⟩) ≃ Σ v : routes q, proposals i q v),
    {path : ((z : {ext // PositiveExterior G₁ args readerPin clockWidth ext}) × ((u : Fin (R+1)) →
      (U z u).Prefix (cube.cubeID e))) ≃ domains //
      ∀ (i : Fin pins → Bool) (q : Hist) (v : routes q) (c : claims) (r₀ : proposals i q v),
        let z := path.symm ⟨i,q,v,c,r₀⟩
        let received := (routed i q c).symm ⟨v,r₀⟩
        z.1.val=received.2.1.val ∧ ∀ u, (z.2 u).2.val=(received.2.2 u).val ∧
          List.ofFn (z.2 u).1=List.ofFn (((G₁).jointGuess ib hb sb).symm i u)} := by
  intro U ib hb sb routed
  exact decoder.bare routes proposals routed

/-- Certifying the post-call cells and joint clock now gives the same
selected row directory on the actual positive team bodies. -/
noncomputable def signedSupportedIssuedPrefixes (hdr : layout.header=headers)
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
    {path : JointBeforeCells (BootedPinStart.supportedTeam (cube.cubeID e) B₀ limit burst privateRoom next) ≃ domains //
      ∀ (i : Fin pins → Bool) (q : Hist) (v : routes q) (c : claims) (r₀ : proposals i q v),
        let z := path.symm ⟨i,q,v,c,r₀⟩
        let received := (routed i q c).symm ⟨v,r₀⟩
        z.1.val=received.2.1.val ∧ ∀ u, (z.2 u).2.val=(received.2.2 u).val ∧
          List.ofFn (z.2 u).1=List.ofFn (((G₁).jointGuess ib hb sb).symm i u)} := by
  intro U ib hb sb mac limit burst privateRoom next routed
  exact decoder.supported limit burst privateRoom next routes proposals routed

local notation3 (prettyPrint := false) "nativeCap" =>
  declarationCap (arena).n (arena).header.d (arena).header.blocks (arena).b (arena).h (arena).s

local notation3 (prettyPrint := false) "eligible(" q ")" =>
  plan.signedBroadcastAllowed p fit W position code sites edges ports table words good free count hp q cube α ξ
    calibrated lit hd number parameters arenaBase profileBits

set_option maxHeartbeats 2600000 in
/-- At the selected frozen history the complete physical pin, raw cube and
owned report exteriors give exactly the route and proposals of its actual
signed core directory. The candidate retains its own observed scanner inverse. -/
noncomputable def signedAdmittedRouting
    {room : ∀ u, ((G₁).transferFrame u (args u).header (args u).dst).Fits clockWidth (base u)}
    (hdr : layout.header=JointHeader.PositiveFields.width profileBits cube.pred (BorderVNP.Cube.alphabet α (k+1))
      nativeCap (R+1) columns tallyWidth)
    (enc : Hist ↪ (Fin profileBits → Bool))
    (B₀ : (z : {ext // PositiveExterior G₁ args readerPin clockWidth ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G₁ pub reg args readerPin z.val u)
    (i : Fin pins → Bool) (q : Hist) (claim : claims) (admitted : plan.AdmitsSignedPackets cube α ξ count calibrated)
    (template : DiagonalTallyPacketEmit.Frame) (entries : ℕ) :
    let U := fun z u => (B₀ z u).start
    let ib := fun u => (args u).ibase
    let hb := fun u => (args u).hbase
    let sb := fun u => (args u).starbase
    AdmittedPinnedFrames G₁ args readerPin layout fixed hw agreeWidth base room arena hdr U ib hb sb
          (fun _ _ => rfl) (cube.cubeID e) (core(q)).owners (rsrc(q)) i (enc q) claim (eligible(q)) template entries →
      (∀ c, ParsedPreCall G₁ args readerPin layout fixed hw agreeWidth base room hdr U ib hb sb (fun _ _ => rfl)
          (cube.cubeID e) i ⟨enc q,c,claim⟩ → LocalRow.declarationInRange c ∧ (eligible(q)) c) →
      (Σ c : Broadcast cube.pred (BorderVNP.Cube.alphabet α (k+1)) nativeCap,
        ParsedPreCall G₁ args readerPin layout fixed hw agreeWidth base room hdr U ib hb sb (fun _ _ => rfl)
          (cube.cubeID e) i ⟨enc q,c,claim⟩) ≃ Σ v : routes q, proposals i q v := by
  intro U ib hb sb candidates checked
  have honest := plan.signedBroadcastAllowed_honest p fit W position code sites edges ports table words good seeds free
    count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits admitted
  exact (candidates.preparations G₁ args readerPin layout fixed hw agreeWidth base room arena hdr U ib hb sb
    (fun _ _ => rfl) (cube.cubeID e) (core(q)).owners (rsrc(q)) i (enc q) claim (eligible(q)) template entries checked honest).trans
    (plan.signedPinnedReportProposals p fit W position code sites edges ports table words good seeds free count pos
      num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin)

/-- At this calibrated history the original decoder is the physical routed preparation
followed by reading the pinned selection and the received reports on all its teams. -/
theorem signedAdmittedRouting_eq_reindexed
    {room : ∀ u, ((G₁).transferFrame u (args u).header (args u).dst).Fits clockWidth (base u)}
    (hdr : layout.header=JointHeader.PositiveFields.width profileBits cube.pred (BorderVNP.Cube.alphabet α (k+1))
      nativeCap (R+1) columns tallyWidth)
    (enc : Hist ↪ (Fin profileBits → Bool))
    (B₀ : (z : {ext // PositiveExterior G₁ args readerPin clockWidth ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G₁ pub reg args readerPin z.val u)
    (i : Fin pins → Bool) (q : Hist) (claim : claims) (admitted : plan.AdmitsSignedPackets cube α ξ count calibrated)
    (template : DiagonalTallyPacketEmit.Frame) (entries : ℕ) :
    let U := fun z u => (B₀ z u).start
    let ib := fun u => (args u).ibase
    let hb := fun u => (args u).hbase
    let sb := fun u => (args u).starbase
    ∀ (candidates : AdmittedPinnedFrames G₁ args readerPin layout fixed hw agreeWidth base room arena hdr U ib hb sb
          (fun _ _ => rfl) (cube.cubeID e) (core(q)).owners (rsrc(q)) i (enc q) claim (eligible(q)) template entries)
      (checked : ∀ c, ParsedPreCall G₁ args readerPin layout fixed hw agreeWidth base room hdr U ib hb sb
        (fun _ _ => rfl) (cube.cubeID e) i ⟨enc q,c,claim⟩ → LocalRow.declarationInRange c ∧ (eligible(q)) c),
      let honest := plan.signedBroadcastAllowed_honest p fit W position code sites edges ports table words good seeds free
        count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits admitted
      plan.signedAdmittedRouting (R:=R) (r:=r) (pins:=pins) (k:=k) (tallyWidth:=tallyWidth) (columns:=columns)
        p fit W position code sites edges ports table words good seeds free count pos num hp cube α ξ calibrated lit hd
        number parameters arenaBase profileBits frame origin pub reg args readerPin layout fixed hw agreeWidth base
        (room:=room) hdr enc B₀ i q claim admitted template entries candidates checked =
      (candidates.preparations G₁ args readerPin layout fixed hw agreeWidth base room arena hdr U ib hb sb
        (fun _ _ => rfl) (cube.cubeID e) (core(q)).owners (rsrc(q)) i (enc q) claim (eligible(q)) template entries
        checked honest).trans
        (plan.signedPinnedReportProposals p fit W position code sites edges ports table words good seeds free count
          pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin) := by
  intro U ib hb sb candidates checked honest
  dsimp only [signedAdmittedRouting,U,ib,hb,sb,honest]

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
