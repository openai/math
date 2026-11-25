import OAI.Computability.BorderVNP.DiagonalSignedCandidateCubeWords
import OAI.Computability.BorderVNP.DiagonalFrozenOwnedReportData

/-! # Physical report ownership on the candidate's actual publication -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.GroupWeights Cube.LabelIndex Cube.Tally
open CubeHeaderInstall CubeArena TeamContraction TeamContraction.JointHeader LocalRow Transmission
open VPVNP.BurstRAM
open Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.RoutingOutputs
open VPVNP.VerifierNetwork Packing.Inherited Packing.BottomReports DiagonalTallyCellReports
open DiagonalTallyAllocation ReportDirectory DiagonalResidueRAM FiniteEvaluator GeometryFrameEncoding
open scoped Classical

variable {D w R X : ℕ} {P A : Type} [Fintype P] [Fintype A] {bits : P → ℕ}
    (N : Network D P bits) (t : SignedTaskArena.Layout) (cell : N.Site → Fin t.cube.cells)
    (recv : A → Fin t.cube.cells) (size : A → ℕ) {D₀ : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w} {mem : Memory w}
    {initialBase receivingBase : ℕ} {pins : Pins.Layout} {fields : Pins.ProcessorFields pins} {f : BroadcastFrame}
    {guess : ℕ → Bool} {I : Type*} [Fintype I] {resides : I → Fin t.cube.cells} {keyID : I ↪ ℕ} {sizes : I → ℕ}
    {representative : ℕ → Fin (R+1)} {group : Fin t.cube.header.d → Fin (R+1)}
    (raw : Broadcast t.cube.n t.cube.header.d t.cube.header.cap)
local notation3 (prettyPrint := false) "dec" => Prod.mk (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1))
  (fun (p : Sym2 (Fin t.cube.header.d)) (j : Fin (t.cube.n+1)) => readCode (t.cube.header.cap+1) (raw.2 p j))
variable (site : CandidateSite (X:=X) t.cube D₀ pp lp raw representative
      (Prod.mk (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1))
        (fun (p : Sym2 (Fin t.cube.header.d)) (j : Fin (t.cube.n+1)) => readCode (t.cube.header.cap+1) (raw.2 p j)))
      group initialBase receivingBase pins fields f guess pub mac reg mem resides keyID sizes N cell recv size)
    {origin : ℕ}
local notation3 (prettyPrint := false) "frame" => (pub 0).val
local notation "table" => bases origin t.cube.cables t.cube.cells D₀.entries
local notation "ctl" => controlsBase origin t.cube.cables t.cube.cells D₀.entries (D₀.teams*D₀.sites)
local notation3 (prettyPrint := false) "labels" => meanPackedLabel N cell recv size (List.finRange t.cube.cells)
  t.cube.n t.cube.header.d ((Nat.succ_pos 1).trans_le site.input.alphabet)
local notation3 (prettyPrint := false) "owns" => greedyOwner R t.cube.b t.cube.s labels recv size
variable {cb lb polyWord o ns np : ℕ} {σ : Type} [Fintype σ] (state : N.Site → Site)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin t.cube.cables) (portID : P ↪ Fin np)
    (F : Fields ns t.cube.cables np t.cube.cells cb lb polyWord σ) {x : σ → Bool}
    (original : Fin D₀.entries → N.Site) (live : Fin (D₀.teams*D₀.sites) → P)
    (team : Fin (R+1)) (host : Fin D₀.entries → Fin t.cube.cells)
    (header : Fin D₀.entries → BundleHeader) (body factors : Fin D₀.entries → List CellSparse.Factor)
    (src : Fin D₀.entries → ℕ → Bool) {bankBits gap : ℕ}
local notation "aux" => (fun v => Site.size (state v))
local notation "key" => (fun v => Fin.val (cell v))
local notation "report" => reportLayout t.before t.after frame ctl t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation "bd" => t.bundleLayout frame ctl D₀.entries
local notation "rows" => t.controlRows team.val frame (Bases.ends table) ctl (Bases.livePairs table) (D₀.teams*D₀.sites)
local notation3 (prettyPrint := false) "payload" b => fun j => physicalBundle (header j) (body j) (factors j) (b j)

local notation3 (prettyPrint := false) "reported" => fun j : Fin D₀.entries => physicalBundle (header j) (body j) (factors j) (src j)
local notation3 (prettyPrint := false) "bundlesAt" c => (Packing.BundleDirectory.sourceRows host c).map reported

set_option maxHeartbeats 2200000 in
/-- The original signed geometry, the actual directory scan and the report
registers all belong to this particular candidate site. Its own writer
provides the schedule, label rows and the three report pointers. -/
theorem CandidateSite.owned_local_reports
    (old : Fin 81 → Word w) (pinned subtotal : ℕ)
    (previous : site.old=PackedHistoryCircuit.routingExtension (t.extension pinned f.team subtotal old)
      D₀ origin t.cube.cables t.cube.cells) (address : site.control=ctl)
    (descriptorFit : t.after.descriptors<2^w) (paramFit : t.p.parameters<2^w)
    (q : NativeAssignments.Routed (b := t.cube.b) (s := t.cube.s) owns)
    (spells : ∀ h : t.cube.header.cap=declarationCap t.cube.n t.cube.header.d t.cube.header.blocks t.cube.b t.cube.h t.cube.s,
      h ▸ raw = broadcast t.cube.b t.cube.s q.1)
    (slot : LiveBit N cell ↪ Slot t.cube.n t.cube.header.d t.cube.header.blocks (t.cube.h*t.cube.b))
    {ownedPub : Arg → Word w} {ownedMac : TeamOpcode.Macros w 8} {ownedReg : Bank w} {out : Memory w}
    (control : FrozenControlEntry t
      (t.openInputs team.val frame (Bases.ends table) ctl (Bases.livePairs table) (D₀.teams*D₀.sites)
        D₀.entries bankBits host header) frame (ownedPub 0).val ctl (Bases.ends table) w
        (fun c => suppliedSize N cell c) (readings site.receipt.history.dataInput) (readings out))
    (space : t.OpenRoom frame (Bases.ends table) ctl (Bases.livePairs table) (D₀.teams*D₀.sites) D₀.entries (2^bankBits) w)
    (image : Image F (siteID ∘ original) (portID ∘ live) x origin (readings site.geometry))
    (net : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c,(F.cells c).val=c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^polyWord)
    (privatePlace : (privateLayout frame origin t.cube.cables t.cube.cells D₀.entries D₀.description gap).Image
      (readings site.geometry) D₀.entries (readings site.middle))
    (low : frame+112 ≤ receivingBase) (reserve : receivingBase+7*D₀.candidates ≤ origin)
    (rest : Frame σ (Outputs o polyWord)) (wf : polyWord ≤ w)
    (words : ∀ i : Fin ((t.cube.cells+(D₀.entries+t.cube.cells))+o),
      site.geometry (origin+t.cube.cables*3+Packing.RoutingOutputs.count t.cube.cables t.cube.cells D₀.entries (D₀.teams*D₀.sites)+i.val)=
        word w (ParseBatchSort.value fun j => (withPrivateViews F (siteID ∘ original) rest).eval x (.inl (i,j))))
    (digits : ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool) :
    let ret := OpenSuffix.hostImage frame (readings out)
    let cs := directoryCells bd rows report host reported (grouped bd host reported ret) digits
    SameReportCells cs
      ((routedSourceReports t.cube N cell owns slot labels (fun _ => report) host (payload (fun _ _ => false))
        (fun c => suppliedSize N key c) (fun c => guessedSize N key c+siteSize N key c aux)).cells q team) ∧
    ((∀ c : Fin t.cube.cells, suppliedSize N cell c+gap≤t.cube.cellStride) →
    (∀ c : Fin t.cube.cells, t.p.report.gadgets*t.p.report.countWidth+weightedCopies (bundlesAt c.val)≤gap) →
    (∀ c : Fin t.cube.cells, supplementWords (bundlesAt c.val)≤t.p.report.supplementStride) →
    (∀ j : Fin D₀.entries,(reported j).positions.length≤t.p.report.marked) →
    (∑ j,(reported j).useCount)≤t.p.report.uses →
    (∀ j,(∃ c∈cs,(host j).val=c.number) → (reported j).delivered report D₀.description ret ∧
      (reported j).SiteRoom report w D₀.description) →
    SiteIntervals cs D₀.description t.cube.cellStride →
    (∀ c∈cs,c.privateWires+c.supplied+c.tailWidth<2^w) →
    t.p.siteWidth≤w → t.p.siteWidth+t.p.bodyCap<2^w →
    ∀ {a b c : ℕ}, t.endAddress w a b c<2^w →
    (∀ (advance : Returns SignedPrep.controls ownedPub ownedMac ownedReg out)
      (reportRun : Returns prepareCellReports ownedPub ownedMac advance.val.2.1 advance.val.2.2),
      PreparedReportInput ownedPub advance.val.2.2 cs t.after.reportCursor D₀.description →
      ReportAllocation t.before t.after (t.cube.cellWriter frame ctl (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1)))
        report cs t.after.reportCursor →
      Nonempty (ArgumentInput ownedPub ownedMac reportRun.val.2.1 reportRun.val.2.2)) →
    ∃ candidate : LocalReportData ownedPub ownedMac ownedReg out,
      SameReportCells candidate.cells
        ((routedSourceReports t.cube N cell owns slot labels (fun _ => report) host (payload (fun _ _ => false))
          (fun c => suppliedSize N key c) (fun c => guessedSize N key c+siteSize N key c aux)).cells q team)) := by
  let actual := Packing.Directory.ISA.publish site.middle (pub 0).val receivingBase (D₀.directory pp lp)
  have signed := site.input
  rw [previous] at signed
  have native := site.receipt.native_entry t site.placement f old origin t.cube.cables t.cube.cells pinned subtotal
    site.fresh site.gates site.outputs site.width site.off site.ell site.control site.profile site.claims site.pad raw
    site.actual signed
  have operands := site.receipt.report_input_words t f old origin t.cube.cables t.cube.cells pinned subtotal site.fresh
    site.gates site.outputs site.width site.off site.ell site.control site.profile site.claims site.pad raw site.actual signed
    descriptorFit paramFit
  have rawInput := site.input
  rw [address] at rawInput native
  have nativeAt : NativeEntry t.cube frame ctl dec.1 R
      (powerHeaderImage t.cube f.dst (readings site.receipt.labeling.val.2.2))
      (readings actual) (readings site.receipt.history.dataInput) :=
    Eq.mp (congrArg (fun m : Memory w => NativeEntry t.cube frame ctl dec.1 R
      (powerHeaderImage t.cube f.dst (readings site.receipt.labeling.val.2.2))
      (readings m) (readings site.receipt.history.dataInput)) site.actual) native
  let scan : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub mac site.published.val.2.1 actual :=
    ⟨site.receipt.labeling.val,Eq.mp (congrArg (fun m : Memory w =>
      Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) site.published.val.2.1 m
        site.receipt.labeling.val.1 site.receipt.labeling.val.2.1 site.receipt.labeling.val.2.2) site.actual)
          site.receipt.labeling.property⟩
  have actualRows := site.rows
  rw [site.actual] at actualRows
  obtain ⟨_,_,cables,delivery,placed⟩ := actualRows
  exact owned_local_report_source N t cell recv size f site.old site.fresh site.gates site.outputs site.width site.off site.ell
    mac site.published.val.2.1 site.profile site.claims site.pad X raw rawInput state siteID edgeID portID F original live team
    host header body factors src cables delivery.toEmbedding placed scan q spells slot _ nativeAt control operands space image net codes
    fit privatePlace low reserve rest wf words digits

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
