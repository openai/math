import OAI.Computability.BorderVNP.DiagonalSignedProfileReportRows
import OAI.Computability.BorderVNP.DiagonalRoutedReceivingOwner

/-! # Physical selected-row source agreement on the actual pinned signed route -/

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
  meanPackedLabel N cell recv size ((List.finRange (dir).cells).map (number).symm) t.cube.n t.cube.header.d
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

set_option maxHeartbeats 1500000 in
/-- For the same routed selector and original signed profile, the report
scanner's directory is the source list ordered by the actual greedy owner,
with the true network widths at every occupied row. -/
theorem pinned_signed_report_source
    (edgeOrd : N.CrossingEdge cell ↪ Fin (dir).cableCount) (dataOrd : A ↪ Fin (dir).deliveryCount)
    (traffic : RowPlacement (networkRows N cell recv size) (fromTables dir (readings mem) room.labels.endpoints)
      number (edgeOrd.sumMap dataOrd))
    (z : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub mac reg mem)
    (q : NativeAssignments.Routed (b := t.cube.b) (s := t.cube.s) owns)
    (spells : ∀ h : t.cube.header.cap=declarationCap t.cube.n t.cube.header.d t.cube.header.blocks t.cube.b t.cube.h t.cube.s,
      h ▸ raw = broadcast t.cube.b t.cube.s q.1)
    (slot : LiveBit N cell ↪ Slot t.cube.n t.cube.header.d t.cube.header.blocks (t.cube.h*t.cube.b))
    (written returned : ℕ → ℕ)
    (entry : NativeEntry t.cube frame ctl (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1)) R
      (powerHeaderImage t.cube f.dst (readings z.val.2.2)) (readings mem) written)
    (keep : CubeAllocation.HostRetention t.cube frame (readings mem) written returned)
    (place : OpenSuffix.Placement
      (t.openInputs team.val frame (Bases.ends table) ctl (Bases.livePairs table) (D₀.teams*D₀.sites) D₀.entries bankBits host header)
      t.cube t.before frame returned)
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
    SameReportCells (directoryCells bd rows report host (payload src)
      (grouped bd host (payload src) (OpenSuffix.hostImage frame returned)) digits)
      ((routedSourceReports t.cube N cell owns slot labels (fun _ => report) host (payload (fun _ _ => false))
        (fun c => suppliedSize N key c) (fun c => guessedSize N key c+siteSize N key c aux)).cells q team) := by
  have chosen := pinned_routed_owner_word N t.cube cell recv size f old fresh gates outputs width off ell ctl mac reg G claims
    pad X raw room edgeOrd dataOrd traffic z q (spells _)
  exact t.signedProfile_reportSource N cell state siteID edgeID portID F D₀ original live pp lp team _ host header body
    factors src _ written returned entry keep place space _ chosen image net codes fit privatePlace low reserve rest wf words digits

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
