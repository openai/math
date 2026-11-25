import OAI.Computability.BorderVNP.DiagonalPinnedSignedReportSource
import OAI.Computability.BorderVNP.DiagonalFrozenPaddingControls
import OAI.Computability.BorderVNP.DiagonalSignedPhysicalReportData

/-! # Private reports on one genuine returned owned tuple -/

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

variable {D w R : ℕ} {P A : Type} [Fintype A] {bits : P → ℕ} (N : Network D P bits)
    (t : SignedTaskArena.Layout) (cell : N.Site → Fin t.cube.cells) (recv : A → Fin t.cube.cells) (size : A → ℕ)
    {D₀ : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {pub : Arg → Word w} {base : ℕ}
    {slotted : Memory w} (f : BroadcastFrame) (old : Fin 81 → Word w)
    (fresh gates outputs width off ell : ℕ) {origin : ℕ} (mac : TeamOpcode.Macros w 8) (reg : Bank w)
    (G : List Bool) (claims : List (List Bool)) (pad X : ℕ)
    (raw : Broadcast t.cube.n t.cube.header.d t.cube.header.cap)
local notation3 (prettyPrint := false) "mem" => Packing.Directory.ISA.publish slotted (pub 0).val base (D₀.directory pp lp)
local notation3 (prettyPrint := false) "frame" => (pub 0).val
local notation3 (prettyPrint := false) "dir" => LabelIndex.layout frame (readings mem)
local notation "table" => bases origin t.cube.cables t.cube.cells D₀.entries
local notation "ctl" => controlsBase origin t.cube.cables t.cube.cells D₀.entries (D₀.teams*D₀.sites)
variable (room : PinnedRawInput (ar := t.cube) (D := D₀) (pp := pp) (lp := lp) (pub := pub) (slotted := slotted) (base := base)
    f old fresh gates outputs width off ell
      (controlsBase origin t.cube.cables t.cube.cells D₀.entries (D₀.teams*D₀.sites)) G claims pad raw R X)
local notation3 (prettyPrint := false) "number" => finCongr room.cells.symm
local notation3 (prettyPrint := false) "labels" =>
  meanPackedLabel N cell recv size (List.finRange t.cube.cells) t.cube.n t.cube.header.d
    ((Nat.succ_pos 1).trans_le room.alphabet)
local notation3 (prettyPrint := false) "owns" => greedyOwner R t.cube.b t.cube.s labels recv size


variable {cb lb polyWord o ns np : ℕ} {σ : Type} [Fintype P] [Fintype σ] (state : N.Site → Site)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin t.cube.cables) (portID : P ↪ Fin np)
    (F : Fields ns t.cube.cables np t.cube.cells cb lb polyWord σ) {x : σ → Bool}
    (original : Fin D₀.entries → N.Site) (live : Fin (D₀.teams*D₀.sites) → P)
    (team : Fin (R+1)) (host : Fin D₀.entries → Fin t.cube.cells)
    (header : Fin D₀.entries → BundleHeader) (body factors : Fin D₀.entries → List CellSparse.Factor)
    (src : Fin D₀.entries → ℕ → Bool) {bankBits gap : ℕ} {profile : Memory w}
local notation "aux" => (fun v => Site.size (state v))
local notation "key" => (fun v => Fin.val (cell v))
local notation "report" => reportLayout t.before t.after frame ctl t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation "bd" => t.bundleLayout frame ctl D₀.entries
local notation "rows" => t.controlRows team.val frame (Bases.ends table) ctl (Bases.livePairs table) (D₀.teams*D₀.sites)
local notation3 (prettyPrint := false) "payload" b => fun j => physicalBundle (header j) (body j) (factors j) (b j)

local notation3 (prettyPrint := false) "reported" => fun j : Fin D₀.entries => physicalBundle (header j) (body j) (factors j) (src j)
local notation3 (prettyPrint := false) "bundlesAt" c => (Packing.BundleDirectory.sourceRows host c).map reported

set_option maxHeartbeats 1800000 in
/-- On the same owned memory that supplied the successful control scan, take
the actual frozen report directory and its physical sparse continuations.
The sampling program reads exactly the selected source rows in ordinal order. -/
theorem owned_local_report_source
    (edgeOrd : N.CrossingEdge cell ↪ Fin (dir).cableCount) (dataOrd : A ↪ Fin (dir).deliveryCount)
    (traffic : RowPlacement (networkRows N cell recv size) (fromTables dir (readings mem) room.labels.endpoints)
      number (edgeOrd.sumMap dataOrd))
    (z : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub mac reg mem)
    (q : NativeAssignments.Routed (b := t.cube.b) (s := t.cube.s) owns)
    (spells : ∀ h : t.cube.header.cap=declarationCap t.cube.n t.cube.header.d t.cube.header.blocks t.cube.b t.cube.h t.cube.s,
      h ▸ raw = broadcast t.cube.b t.cube.s q.1)
    (slot : LiveBit N cell ↪ Slot t.cube.n t.cube.header.d t.cube.header.blocks (t.cube.h*t.cube.b))
    (written : ℕ → ℕ) {ownedPub : Arg → Word w} {ownedMac : TeamOpcode.Macros w 8}
    {ownedReg : Bank w} {out : Memory w}
    (entry : NativeEntry t.cube frame ctl (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1)) R
      (powerHeaderImage t.cube f.dst (readings z.val.2.2)) (readings mem) written)
    (control : FrozenControlEntry t
      (t.openInputs team.val frame (Bases.ends table) ctl (Bases.livePairs table) (D₀.teams*D₀.sites)
        D₀.entries bankBits host header) frame (ownedPub 0).val ctl (Bases.ends table) w
        (fun c => suppliedSize N cell c) written (readings out))
    (pointers : written (frame+44)=t.after.descriptors ∧ written (frame+81)=t.cube.stop ∧
      written (frame+95)=t.p.parameters)
    (space : t.OpenRoom frame (Bases.ends table) ctl (Bases.livePairs table) (D₀.teams*D₀.sites) D₀.entries (2^bankBits) w)
    (image : Image F (siteID ∘ original) (portID ∘ live) x origin (readings profile))
    (net : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c,(F.cells c).val=c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^polyWord)
    (privatePlace : (privateLayout frame origin t.cube.cables t.cube.cells D₀.entries D₀.description gap).Image
      (readings profile) D₀.entries (readings slotted))
    (low : frame+112 ≤ base) (reserve : base+7*D₀.candidates ≤ origin)
    (rest : Frame σ (Outputs o polyWord)) (wf : polyWord ≤ w)
    (words : ∀ i : Fin ((t.cube.cells+(D₀.entries+t.cube.cells))+o),
      profile (origin+t.cube.cables*3+Packing.RoutingOutputs.count t.cube.cables t.cube.cells D₀.entries (D₀.teams*D₀.sites)+i.val)=
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
  intro ret cs
  have keep : CubeAllocation.HostRetention t.cube frame (readings mem) written (readings out) :=
    ⟨control.retained.primary,fun i hi sep₁ sep₂ => (control.retained.lower i hi sep₁ sep₂).trans (entry.low i hi),
      control.retained.tables⟩
  have normalize {a b : ℕ} (eqn : b=a) : (List.finRange a).map (finCongr eqn).symm=List.finRange b := by
    subst b
    simp
  have sourceRows := pinned_signed_report_source (o:=o) (x:=x) (bankBits:=bankBits) (gap:=gap) (profile:=profile) N t cell recv size f old fresh gates outputs width off ell mac reg G
    claims pad X raw room state siteID edgeID portID F original live team host header body factors src edgeOrd dataOrd traffic z
  have roster : (List.finRange (dir).cells).map (number).symm=List.finRange t.cube.cells := normalize room.cells.symm
  rw [roster] at sourceRows
  have cells := sourceRows q spells slot written (readings out) entry keep control.placement space image net codes fit
    privatePlace low reserve rest wf words digits
  refine ⟨cells,?_⟩
  intro allocation charges supplement marked expanded delivered intervals privateFits siteWidth fieldsWidth a b c limit args
  have receive (j : Fin t.cube.cells) :
      readings out ((Bases.ends table)+2*t.cube.cables+j.val)+
        (t.p.report.gadgets*t.p.report.countWidth+weightedCopies (bundlesAt j.val))≤t.cube.cellStride := by
    rw [control.receive]
    exact (Nat.add_le_add_left (charges j) _).trans (allocation j)
  have preparation := t.signedReportPreparation (mac:=ownedMac) (s:=ownedReg) host reported digits
    (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1)) D₀.description control.ready control.placement space control.frame
    control.controlWord (control.report_inputs pointers) control.controls control.frameEnd receive supplement marked expanded
    delivered intervals privateFits siteWidth fieldsWidth limit
  let data := t.signedLocalReportData host reported digits
    (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1)) D₀.description control.ready control.placement space control.frame
    control.controlWord (control.report_inputs pointers) control.controls control.frameEnd receive supplement marked expanded
    delivered intervals privateFits siteWidth fieldsWidth limit
    (fun ret reportRun => args ret reportRun (preparation.2 ret) preparation.1)
  exact ⟨data,cells⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
