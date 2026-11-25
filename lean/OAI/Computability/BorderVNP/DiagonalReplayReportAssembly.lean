import OAI.Computability.BorderVNP.DiagonalReplayReportStages

/-! # The issued report data on a measured return of the owned scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open _root_.OAI.Computability.BorderVNP.Cube Physical Tally MeanChoice GroupWeights LocalRow SignedPrep DiagonalTallyPacketEmit
open Crossing Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.RoutingOutputs
open Packing.BottomReports DiagonalTallyCellReports DiagonalTallyAllocation ReportDirectory

variable {D w R X r teams pinsCount link inner n : ℕ} {Edge : Type} {G : Wiring R r teams pinsCount link inner n Edge}
    {L : WireLayout (R+1) r link} {header : List Bool} {pin : Fin pinsCount → Bool} (fixed : Block (R+1))
    (t : SignedTaskArena.Layout) {P A : Type} [Fintype P] [Fintype A] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin t.cube.cells) (recv : A → Fin t.cube.cells) (size : A → ℕ)
    {d : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w} {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    {initialBase receiving : ℕ} {pins : Fin (R+1) → Pins.Layout}
    {fields : HeaderExterior L header → (u : Fin (R+1)) → Pins.ProcessorFields (pins u)}
    {bf : Fin (R+1) → BroadcastFrame} {guess : Fin (R+1) → ℕ → Bool} {I : Type*} [Fintype I]
    {resides : I → Fin t.cube.cells} {key : I ↪ ℕ} {sizes : I → ℕ}
    {representative : ℕ → Fin (R+1)} {group : Fin t.cube.header.d → Fin (R+1)}
    (raw : Broadcast t.cube.n t.cube.header.d t.cube.header.cap) (positive : 0<t.cube.header.d)
    (site : ∀ z u, CandidateSite (X:=X) t.cube d pp lp raw representative
      (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1),fun p j => readCode (t.cube.header.cap+1) (raw.2 p j))
      group initialBase receiving (pins u) (fields z u) (bf u) (guess u) (pub z u) (mac z u) (reg z u) (mem z u)
      resides key sizes N cell recv size)
    (F : PreparationFrame G L t.cube
      (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1),fun p j => readCode (t.cube.header.cap+1) (raw.2 p j))
      header pin pub mac reg mem)
    (template : Frame) (count : ℕ) (origin : Fin (R+1) → ℕ)
    {cb lb widthO outputs ns np : ℕ} {σ : Type} [Fintype σ] (state : N.Site → Packing.Inherited.Site)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin t.cube.cables) (portID : P ↪ Fin np)
    (geom : Fields ns t.cube.cables np t.cube.cells cb lb widthO σ)
    (input : HeaderExterior L header → Fin (R+1) → σ → Bool)
    (original : Fin d.entries → N.Site) (live : Fin (d.teams*d.sites) → P)
    (host : Fin d.entries → Fin t.cube.cells) (hdr : Fin d.entries → BundleHeader)
    (body factors : Fin d.entries → List CellSparse.Factor) {b gap : ℕ}
    (slot : LiveBit N cell ↪ Slot t.cube.n t.cube.header.d t.cube.header.blocks (t.cube.h*t.cube.b))

local notation3 (prettyPrint := false) "decl" => Prod.mk (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1))
  (fun (p : Sym2 (Fin t.cube.header.d)) (j : Fin (t.cube.n+1)) => readCode (t.cube.header.cap+1) (raw.2 p j))
local notation3 (prettyPrint := false) "label" => meanPackedLabel N cell recv size (List.finRange t.cube.cells)
  t.cube.n t.cube.header.d positive
local notation3 (prettyPrint := false) "owns" => greedyOwner R t.cube.b t.cube.s label recv size
local notation3 (prettyPrint := false) "frozen" => fun j : Fin d.entries => physicalBundle (hdr j) (body j) (factors j) (fun _ => false)
local notation3 (prettyPrint := false) "ctl(" u ")" => controlsBase (origin u) t.cube.cables t.cube.cells d.entries (d.teams*d.sites)
local notation3 (prettyPrint := false) "report(" x "," u ")" => reportLayout t.before t.after x (ctl(u)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation3 (prettyPrint := false) "source" => routedSourceReports t.cube N cell owns slot label
  (fun u => report(initialBase,u)) host frozen (fun c => suppliedSize N (fun v => (cell v).val) c)
  (fun c => guessedSize N (fun v => (cell v).val) c+siteSize N (fun v => (cell v).val) c (fun v => ((state v).size)))
local notation3 (prettyPrint := false) "total" => count+t.cube.header.d.choose 2

local notation3 (prettyPrint := false) "opening(" z "," q "," rows ")" =>
  CandidateReportOpening N t cell recv size raw (site z) origin state host hdr body factors slot q
    (b:=b) (ep:=(rows).pub) (em:=(rows).macros) (er:=(rows).finalRegs) (out:=(rows).output)
local notation3 (prettyPrint := false) "delivered(" z "," q "," rows ")" =>
  CandidateBundleDelivery N t cell recv size raw (site z) origin state host hdr body factors (fun _ _ _ => false)
    slot (fun _ _ _ _ => false) q (out:=(rows).output)
local notation3 (prettyPrint := false) "arguments(" z "," q "," rows ")" =>
  CandidateReportArguments N t cell recv size raw (site z) origin state host hdr body factors (fun _ _ _ => false)
    slot (fun _ _ _ _ => false) q (ep:=(rows).pub) (em:=(rows).macros) (er:=(rows).finalRegs) (out:=(rows).output)

/-- The three operational facts following the replay of the common packet.
The original bundle traffic and the launch of the private argument are
tested against the same owned scan and its actual output memory. -/
abbrev PreparationFrame.OwnedReportCuts : Prop :=
  ∀ operands : SharedWords t.cube decl, let z := F.replay fixed operands
      ∀ (H : Fin (R+1) → TeamHistory w)
        (delivery : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner
          F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
        delivery.table=F.tab → delivery.row=F.row → SharedWriters delivery F.rows (F.source z.1) →
        (∀ u, (H u).pub=pub z.1 u ∧ (H u).macros=mac z.1 u ∧ (H u).history.val.2=(z.2 u).val.2) →
        (∀ u, Pins.SubstitutionAt (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))
          (F.guess u) (H u).initial) → delivery.receivedRows F.rows F.group=operands.val →
        ∀ (q : Matching t.cube owns decl (delivery.receivedRows F.rows F.group))
          (endRows : TeamRows.Returns (Fin (R+1)) t.cube w),
          OwnedHandoff delivery F.rows (F.source z.1) t.cube decl F.group template t.id total endRows →
          ObservedOwned t.cube decl F.group endRows owns (delivery.receivedRows F.rows F.group) q.val →
          opening(z.1,q.val,endRows) ∧ delivered(z.1,q.val,endRows) ∧ arguments(z.1,q.val,endRows)

/-- The earlier data and the three later observations needed to run the
report processor, ordered by the program that supplies each observation. -/
inductive CandidateReportStage where
  | publication
  | capacity
  | opening
  | delivery
  | arguments

/-- One report observation on the actual shared packet, emitted route and
owned scan. The publication and capacity cases concern the earlier installed
site and are independent of returned report assignments. -/
abbrev PreparationFrame.ReportTest (stage : CandidateReportStage) : Prop :=
  let observed (property : HeaderExterior L header →
      NativeAssignments.Routed (blocks:=t.cube.header.blocks) (K:=t.cube.K) (h:=t.cube.h)
        (b:=t.cube.b) (s:=t.cube.s) owns → TeamRows.Returns (Fin (R+1)) t.cube w → Prop) :=
    ∀ operands : SharedWords t.cube decl, let z := F.replay fixed operands
      ∀ (H : Fin (R+1) → TeamHistory w)
        (delivery : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner
          F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
        delivery.table=F.tab → delivery.row=F.row → SharedWriters delivery F.rows (F.source z.1) →
        (∀ u, (H u).pub=pub z.1 u ∧ (H u).macros=mac z.1 u ∧ (H u).history.val.2=(z.2 u).val.2) →
        (∀ u, Pins.SubstitutionAt (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))
          (F.guess u) (H u).initial) → delivery.receivedRows F.rows F.group=operands.val →
        ∀ (q : Matching t.cube owns decl (delivery.receivedRows F.rows F.group))
          (endRows : TeamRows.Returns (Fin (R+1)) t.cube w),
          OwnedHandoff delivery F.rows (F.source z.1) t.cube decl F.group template t.id total endRows →
          ObservedOwned t.cube decl F.group endRows owns (delivery.receivedRows F.rows F.group) q.val →
          property z.1 q.val endRows
  match stage with
  | .publication => ∀ z, Nonempty (CandidateReportPublication N t cell recv size raw (site z) origin
      siteID portID geom original live (outputs:=outputs) (x:=input z) (b:=b) (gap:=gap))
  | .capacity => ∀ z, NativeAssignments.Routed (blocks:=t.cube.header.blocks) (K:=t.cube.K)
      (h:=t.cube.h) (b:=t.cube.b) (s:=t.cube.s) owns → Nonempty (CandidateReportCapacity
      N t cell recv size raw (site z) origin state siteID edgeID portID geom host hdr body factors
      (fun _ _ _ => false) slot (x:=input z) (gap:=gap))
  | .opening => observed fun z q rows => opening(z,q,rows)
  | .delivery => observed fun z q rows => delivered(z,q,rows)
  | .arguments => observed fun z q rows => arguments(z,q,rows)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1800000 in
/-- A successful owned scan selects its own routed declaration. Combine its
opening, original readback and private launch with the earlier issued output.
The initial report templates have zero private banks. The report guesses
range over every successful return of the actual preparation. -/
theorem PreparationFrame.candidateReportsOnReplay_ofOwnedCuts
    (publication : ∀ z, CandidateReportPublication N t cell recv size raw (site z) origin
      siteID portID geom original live (outputs:=outputs) (x:=input z) (b:=b) (gap:=gap))
    (capacity : ∀ z, NativeAssignments.Routed (blocks:=t.cube.header.blocks) (K:=t.cube.K)
      (h:=t.cube.h) (b:=t.cube.b) (s:=t.cube.s) owns → CandidateReportCapacity N t cell recv size raw (site z) origin state siteID edgeID portID geom host
      hdr body factors (fun _ _ _ => false) slot (x:=input z) (gap:=gap))
    (cuts : F.OwnedReportCuts (b:=b) fixed t N cell recv size raw positive site template count origin state
      host hdr body factors slot) :
    F.CandidateReportsOnReplay (b:=b) (gap:=gap) (outputs:=outputs) fixed t N cell recv size raw positive site
      template count origin state siteID edgeID portID geom input original live host hdr body factors slot := by
  intro operands anchor H delivery table row writers actual guesses received q endRows handoff seen
  obtain ⟨opened, originalReads, privateRun⟩ :=
    cuts operands H delivery table row writers actual guesses received q endRows handoff seen
  let installed := publication anchor.1
  let bounds := capacity anchor.1 q.val
  refine ⟨fun _ _ _ => false, fun _ _ _ _ => false, ⟨{
    old := installed.old
    pin := installed.pin
    subtotal := installed.subtotal
    literal := installed.literal
    address := installed.address
    space := installed.space
    image := installed.image
    place := installed.place
    low := installed.low
    reserve := installed.reserve
    rest := installed.rest
    words := installed.words
    descFit := bounds.descFit
    paramFit := bounds.paramFit
    range := bounds.range
    net := bounds.net
    codes := bounds.codes
    widths := bounds.widths
    fit := bounds.fit
    allocation := bounds.allocation
    charge := bounds.charge
    supp := bounds.supp
    marked := bounds.marked
    uses := bounds.uses
    siteWidth := bounds.siteWidth
    bodyFit := bounds.bodyFit
    a := bounds.a
    k := bounds.k
    l := bounds.l
    endFit := bounds.endFit
    sourceRoom := bounds.sourceRoom q.val
    declared := q.property.1
    opened := opened
    returned := fun pinRun u layout =>
      ⟨originalReads pinRun u layout, privateRun pinRun u layout⟩ }⟩⟩

local notation3 (prettyPrint := false) "test(" side ")" =>
  F.ReportTest (b:=b) (gap:=gap) (outputs:=outputs) fixed t N cell recv size raw positive site template count origin
    state siteID edgeID portID geom input original live host hdr body factors slot side

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1200000 in
/-- Install the earlier geometry and capacity witnesses and use all three
later tests on the identical measured return. -/
theorem PreparationFrame.candidateReportsOnReplay_ofTests
    (publication : test(CandidateReportStage.publication)) (capacity : test(CandidateReportStage.capacity))
    (openingProof : test(CandidateReportStage.opening)) (originalRead : test(CandidateReportStage.delivery))
    (privateInput : test(CandidateReportStage.arguments)) :
    F.CandidateReportsOnReplay (b:=b) (gap:=gap) (outputs:=outputs) fixed t N cell recv size raw positive site
      template count origin state siteID edgeID portID geom input original live host hdr body factors slot := by
  apply F.candidateReportsOnReplay_ofOwnedCuts (b:=b) (gap:=gap) (outputs:=outputs) fixed t N cell recv size raw positive site
    template count origin state siteID edgeID portID geom input original live host hdr body factors slot
    (fun z => Classical.choice (publication z)) (fun z v => Classical.choice (capacity z v))
  intro operands anchor H delivery table row writers actual guesses received q endRows handoff seen
  exact ⟨openingProof operands H delivery table row writers actual guesses received q endRows handoff seen,
    originalRead operands H delivery table row writers actual guesses received q endRows handoff seen,
    privateInput operands H delivery table row writers actual guesses received q endRows handoff seen⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
