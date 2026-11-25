import OAI.Computability.BorderVNP.DiagonalSignedCandidateOwnedReports
import OAI.Computability.BorderVNP.DiagonalSameReportIntervals

/-! # The joint private reports of a returned candidate -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing _root_.OAI.Computability.BorderVNP.Cube Physical MeanChoice GroupWeights LabelIndex Tally
open TeamContraction JointHeader LocalRow Transmission VPVNP.BurstRAM PackedHistoryCircuit
open Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.RoutingOutputs
open VPVNP.VerifierNetwork Packing.Inherited Packing.BottomReports DiagonalTallyCellReports
open DiagonalTallyAllocation ReportDirectory DiagonalResidueRAM FiniteEvaluator GeometryFrameEncoding
open scoped Classical

variable {D w R X : ℕ} {P A : Type} [Fintype P] [Fintype A] {bits : P → ℕ}
    (N : Network D P bits) (t : SignedTaskArena.Layout) (cell : N.Site → Fin t.cube.cells)
    (recv : A → Fin t.cube.cells) (size : A → ℕ) {d : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {pub : Fin (R+1) → Arg → Word w} {mac : Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : Fin (R+1) → Bank w} {mem : Fin (R+1) → Memory w}
    {initialBase receiving : ℕ} {pins : Fin (R+1) → Pins.Layout} {fields : (u : Fin (R+1)) → Pins.ProcessorFields (pins u)}
    {f : Fin (R+1) → BroadcastFrame} {guess : Fin (R+1) → ℕ → Bool} {I : Type*} [Fintype I]
    {resides : I → Fin t.cube.cells} {keyID : I ↪ ℕ} {sizes : I → ℕ}
    {owner : ℕ → Fin (R+1)} {group : Fin t.cube.header.d → Fin (R+1)}
    (raw : Broadcast t.cube.n t.cube.header.d t.cube.header.cap)
    (site : ∀ u, CandidateSite (X:=X) t.cube d pp lp raw owner
      (Prod.mk (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1))
        (fun (p : Sym2 (Fin t.cube.header.d)) (j : Fin (t.cube.n+1)) => readCode (t.cube.header.cap+1) (raw.2 p j)))
      group initialBase receiving (pins u) (fields u) (f u) (guess u) (pub u) (mac u) (reg u) (mem u)
      resides keyID sizes N cell recv size)
    (origin : Fin (R+1) → ℕ)
local notation3 (prettyPrint := false) "base(" u ")" => (pub u 0).val
local notation3 (prettyPrint := false) "tables(" u ")" => bases (origin u) t.cube.cables t.cube.cells d.entries
local notation3 (prettyPrint := false) "ctl(" u ")" => controlsBase (origin u) t.cube.cables t.cube.cells d.entries (d.teams*d.sites)
local notation3 (prettyPrint := false) "label" => meanPackedLabel N cell recv size (List.finRange t.cube.cells)
  t.cube.n t.cube.header.d ((Nat.succ_pos 1).trans_le (site 0).input.alphabet)
local notation3 (prettyPrint := false) "owns" => greedyOwner R t.cube.b t.cube.s label recv size
variable {cb lb polyWord outputs ns np : ℕ} {σ : Type} [Fintype σ] (state : N.Site → Site)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin t.cube.cables) (portID : P ↪ Fin np)
    (F : Fields ns t.cube.cables np t.cube.cells cb lb polyWord σ) {x : Fin (R+1) → σ → Bool}
    (original : Fin d.entries → N.Site) (live : Fin (d.teams*d.sites) → P)
    (host : Fin d.entries → Fin t.cube.cells) (hdr : Fin d.entries → BundleHeader)
    (body factors : Fin d.entries → List CellSparse.Factor) (bank : Fin (R+1) → Fin d.entries → ℕ → Bool)
    {b gap : ℕ} (slot : LiveBit N cell ↪ Slot t.cube.n t.cube.header.d t.cube.header.blocks (t.cube.h*t.cube.b))
local notation3 (prettyPrint := false) "bodyAt(" u ")" => fun j : Fin d.entries => physicalBundle (hdr j) (body j) (factors j) (bank u j)
local notation3 (prettyPrint := false) "frozen" => fun j : Fin d.entries => physicalBundle (hdr j) (body j) (factors j) (fun _ => false)
local notation3 (prettyPrint := false) "key" => fun v : N.Site => (cell v).val
local notation3 (prettyPrint := false) "aux" => fun v : N.Site => Site.size (state v)
local notation3 (prettyPrint := false) "report(" u ")" => reportLayout t.before t.after (base(u)) (ctl(u)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation3 (prettyPrint := false) "source" => routedSourceReports t.cube N cell owns slot label (fun u => report(u))
  host frozen (fun c => suppliedSize N key c) (fun c => guessedSize N key c+siteSize N key c aux)
local notation3 (prettyPrint := false) "prog(" u ")" => t.openInputs (u).val (base(u)) (tables(u)).ends (ctl(u)) (tables(u)).livePairs
  (d.teams*d.sites) d.entries b host hdr
local notation3 (prettyPrint := false) "rows(" u ")" => t.controlRows (u).val (base(u)) (tables(u)).ends (ctl(u)) (tables(u)).livePairs (d.teams*d.sites)

variable {ep : Fin (R+1) → Arg → Word w} {em : Fin (R+1) → TeamOpcode.Macros w 8}
    {er : Fin (R+1) → Bank w} {out : Fin (R+1) → Memory w}
    (counts : Fin (R+1) → ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool)
local notation3 (prettyPrint := false) "ret(" u ")" => OpenSuffix.hostImage (base(u)) (readings (out u))
local notation3 (prettyPrint := false) "cs(" u ")" => directoryCells (t.bundleLayout (base(u)) (ctl(u)) d.entries)
  (rows(u)) (report(u)) host (bodyAt(u)) (grouped (t.bundleLayout (base(u)) (ctl(u)) d.entries) host (bodyAt(u)) (ret(u))) (counts u)
local notation3 (prettyPrint := false) "roster(" u "," c ")" => (Packing.BundleDirectory.sourceRows host (c).val).map (bodyAt(u))

/-- The public packet, its per-team starting states, and the resources for the
private continuation at one owned return. These fields identify actual input
words before any successful reports have been chosen. -/
structure ReturnedCandidateReports (q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns) where
  /-- The 81 words underlying the literal signed task extension at each site. -/
  old : Fin (R+1) → Fin 81 → Word w
  /-- The original raw pin register stored in the task extension. -/
  pin : ℕ
  /-- The width of each signed subtotal claim. -/
  subtotal : ℕ
  literal : ∀ u,(site u).old=routingExtension (t.extension pin (f u).team subtotal (old u)) d (origin u) t.cube.cables t.cube.cells
  address : ∀ u,(site u).control=ctl(u)
  descFit : t.after.descriptors<2^w
  paramFit : t.p.parameters<2^w
  range : declarationInRange raw
  declared : (Scatter.Assignment.Routed.encode owns q).declaration=
      (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1),fun p j => readCode (t.cube.header.cap+1) (raw.2 p j))
  opened : OpenSuffix.ControlFamily (fun u : Fin (R+1) => prog(u)) ep em er out ((source).pins q) ∧
      ∀ u, FrozenControlEntry t (prog(u)) (base(u)) (ep u 0).val (ctl(u)) (tables(u)).ends w
        (fun c => suppliedSize N cell c) (readings (site u).receipt.history.dataInput) (readings (out u))
  space : ∀ u,t.OpenRoom (base(u)) (tables(u)).ends (ctl(u)) (tables(u)).livePairs (d.teams*d.sites) d.entries (2^b) w
  image : ∀ u, Image F (siteID ∘ original) (portID ∘ live) (x u) (origin u) (readings (site u).geometry)
  net : ∀ u,Represents N cell aux siteID edgeID portID F (x u)
  codes : ∀ c,(F.cells c).val=c.val
  widths : ∀ c,guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^polyWord
  place : ∀ u,(privateLayout (base(u)) (origin u) t.cube.cables t.cube.cells d.entries d.description gap).Image
      (readings (site u).geometry) d.entries (readings (site u).middle)
  low : ∀ u,base(u)+112≤receiving
  reserve : ∀ u,receiving+7*d.candidates≤origin u
  /-- The remaining geometry output after the private layout views. -/
  rest : Fin (R+1) → Frame σ (Outputs outputs polyWord)
  fit : polyWord≤w
  words : ∀ u (i : Fin ((t.cube.cells+(d.entries+t.cube.cells))+outputs)),
      (site u).geometry (origin u+t.cube.cables*3+Packing.RoutingOutputs.count t.cube.cables t.cube.cells d.entries
         (d.teams*d.sites)+i.val)=word w (ParseBatchSort.value fun j => (withPrivateViews F (siteID ∘ original) (rest u)).eval (x u) (.inl (i,j)))
  allocation : ∀ c : Fin t.cube.cells,suppliedSize N cell c+gap≤t.cube.cellStride
  charge : ∀ (u : Fin (R+1)) (c : Fin t.cube.cells),t.p.report.gadgets*t.p.report.countWidth+weightedCopies (roster(u,c))≤gap
  supp : ∀ (u : Fin (R+1)) (c : Fin t.cube.cells),supplementWords (roster(u,c))≤t.p.report.supplementStride
  marked : ∀ (u : Fin (R+1)) (j : Fin d.entries),(bodyAt(u) j).positions.length≤t.p.report.marked
  uses : ∀ u : Fin (R+1),(∑ j,(bodyAt(u) j).useCount)≤t.p.report.uses
  siteWidth : t.p.siteWidth≤w
  bodyFit : t.p.siteWidth+t.p.bodyCap<2^w
  /-- The number of input operands in the entry-reader allocation. -/
  a : ℕ
  /-- The number of gates in the entry-reader allocation. -/
  k : ℕ
  /-- The number of gates reserved for the private reader. -/
  l : ℕ
  endFit : t.endAddress w a k l<2^w
  sourceRoom : ∀ u : Fin (R+1), SiteIntervals ((source).cells q u) d.description t.cube.cellStride ∧
      ∀ c∈(source).cells q u,c.privateWires+c.supplied+c.tailWidth<2^w
  returned : (source).pins q → ∀ u : Fin (R+1), SameReportCells (cs(u)) ((source).cells q u) →
      (∀ j, (∃ c∈cs(u),(host j).val=c.number) → (bodyAt(u) j).delivered (report(u)) d.description (ret(u)) ∧
        (bodyAt(u) j).SiteRoom (report(u)) w d.description) ∧
      (∀ (advance : Returns SignedPrep.controls (ep u) (em u) (er u) (out u))
        (run : Returns prepareCellReports (ep u) (em u) advance.val.2.1 advance.val.2.2),
        PreparedReportInput (ep u) advance.val.2.2 (cs(u)) t.after.reportCursor d.description →
        ReportAllocation t.before t.after (t.cube.cellWriter (base(u)) (ctl(u)) (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1)))
          (report(u)) (cs(u)) t.after.reportCursor →
        Nonempty (ArgumentInput (ep u) (em u) run.val.2.1 run.val.2.2))

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1800000 in
/-- Realize all the report paths of a single matching owned assignment. The
directory agreement is available before choosing reports and identifies the
originals actually delivered to each receiving team. -/
theorem candidate_report_family
    (q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns)
    (old : Fin (R+1) → Fin 81 → Word w) (pin subtotal : ℕ)
    (literal : ∀ u,(site u).old=routingExtension (t.extension pin (f u).team subtotal (old u)) d (origin u) t.cube.cables t.cube.cells)
    (address : ∀ u,(site u).control=ctl(u))
    (descFit : t.after.descriptors<2^w) (paramFit : t.p.parameters<2^w)
    (range : declarationInRange raw)
    (declared : (Scatter.Assignment.Routed.encode owns q).declaration=
      (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1),fun p j => readCode (t.cube.header.cap+1) (raw.2 p j)))
    (opened : OpenSuffix.ControlFamily (fun u : Fin (R+1) => prog(u)) ep em er out ((source).pins q) ∧
      ∀ u, FrozenControlEntry t (prog(u)) (base(u)) (ep u 0).val (ctl(u)) (tables(u)).ends w
        (fun c => suppliedSize N cell c) (readings (site u).receipt.history.dataInput) (readings (out u)))
    (space : ∀ u,t.OpenRoom (base(u)) (tables(u)).ends (ctl(u)) (tables(u)).livePairs (d.teams*d.sites) d.entries (2^b) w)
    (image : ∀ u, Image F (siteID ∘ original) (portID ∘ live) (x u) (origin u) (readings (site u).geometry))
    (net : ∀ u,Represents N cell aux siteID edgeID portID F (x u)) (codes : ∀ c,(F.cells c).val=c.val)
    (widths : ∀ c,guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^polyWord)
    (place : ∀ u,(privateLayout (base(u)) (origin u) t.cube.cables t.cube.cells d.entries d.description gap).Image
      (readings (site u).geometry) d.entries (readings (site u).middle))
    (low : ∀ u,base(u)+112≤receiving) (reserve : ∀ u,receiving+7*d.candidates≤origin u)
    (rest : Fin (R+1) → Frame σ (Outputs outputs polyWord)) (fit : polyWord≤w)
    (words : ∀ u (i : Fin ((t.cube.cells+(d.entries+t.cube.cells))+outputs)),
      (site u).geometry (origin u+t.cube.cables*3+Packing.RoutingOutputs.count t.cube.cables t.cube.cells d.entries
         (d.teams*d.sites)+i.val)=word w (ParseBatchSort.value fun j => (withPrivateViews F (siteID ∘ original) (rest u)).eval (x u) (.inl (i,j))))
    (allocation : ∀ c : Fin t.cube.cells,suppliedSize N cell c+gap≤t.cube.cellStride)
    (charge : ∀ (u : Fin (R+1)) (c : Fin t.cube.cells),t.p.report.gadgets*t.p.report.countWidth+weightedCopies (roster(u,c))≤gap)
    (supp : ∀ (u : Fin (R+1)) (c : Fin t.cube.cells),supplementWords (roster(u,c))≤t.p.report.supplementStride)
    (marked : ∀ (u : Fin (R+1)) (j : Fin d.entries),(bodyAt(u) j).positions.length≤t.p.report.marked)
    (uses : ∀ u : Fin (R+1),(∑ j,(bodyAt(u) j).useCount)≤t.p.report.uses)
    (siteWidth : t.p.siteWidth≤w) (bodyFit : t.p.siteWidth+t.p.bodyCap<2^w) {a k l : ℕ} (endFit : t.endAddress w a k l<2^w)
    (sourceRoom : ∀ u : Fin (R+1), SiteIntervals ((source).cells q u) d.description t.cube.cellStride ∧
      ∀ c∈(source).cells q u,c.privateWires+c.supplied+c.tailWidth<2^w)
    (returned : (source).pins q → ∀ u : Fin (R+1), SameReportCells (cs(u)) ((source).cells q u) →
      (∀ j, (∃ c∈cs(u),(host j).val=c.number) → (bodyAt(u) j).delivered (report(u)) d.description (ret(u)) ∧
        (bodyAt(u) j).SiteRoom (report(u)) w d.description) ∧
      (∀ (advance : Returns SignedPrep.controls (ep u) (em u) (er u) (out u))
        (run : Returns prepareCellReports (ep u) (em u) advance.val.2.1 advance.val.2.2),
        PreparedReportInput (ep u) advance.val.2.2 (cs(u)) t.after.reportCursor d.description →
        ReportAllocation t.before t.after (t.cube.cellWriter (base(u)) (ctl(u)) (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1)))
          (report(u)) (cs(u)) t.after.reportCursor →
        Nonempty (ArgumentInput (ep u) (em u) run.val.2.1 run.val.2.2))) :
    ∃ program : Fin (R+1) → OpenSuffix.Inputs,
      OpenSuffix.ControlFamily program ep em er out ((source).pins q) ∧
      ((source).pins q → ∀ u, ∃ data : LocalReportData (ep u) (em u) (er u) (out u),
        SameReportCells data.cells ((source).cells q u)) := by
  refine ⟨_,opened.1,?_⟩
  intro valid u
  have same {cap : ℕ} (h : cap=declarationCap t.cube.n t.cube.header.d t.cube.header.blocks t.cube.b t.cube.h t.cube.s)
      (word : Broadcast t.cube.n t.cube.header.d cap) (validWord : declarationInRange word)
      (decoded : (Scatter.Assignment.Routed.encode owns q).declaration=
        (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) word.1),fun p j => readCode (cap+1) (word.2 p j))) :
      h ▸ word=broadcast t.cube.b t.cube.s q.1 := by
    subst cap
    exact congrArg Subtype.val ((declared_iff_routeBroadcast t.cube owns ⟨word,validWord⟩ q).mp decoded)
  have spells (h : t.cube.header.cap=declarationCap t.cube.n t.cube.header.d t.cube.header.blocks t.cube.b t.cube.h t.cube.s) :=
    same h raw range declared
  have fixed := (site u).owned_local_reports N t cell recv size raw (origin:=origin u) (ownedPub:=ep u) (ownedMac:=em u) (ownedReg:=er u) (out:=out u) state siteID edgeID portID F
    original live u host hdr body factors (bank u) (old u) pin subtotal (literal u) (address u) descFit paramFit q
    spells slot (opened.2 u) (space u) (image u) (net u) codes widths (place u) (low u) (reserve u) (rest u) fit (words u) (counts u)
  obtain ⟨delivered,args⟩ := returned valid u fixed.1
  obtain ⟨intervals,privateFit⟩ := fixed.1.physicalRoom (sourceRoom u).1 (sourceRoom u).2
  exact fixed.2 allocation (charge u) (supp u) (marked u) (uses u) delivered intervals privateFit siteWidth bodyFit endFit args

/-- Apply the accepted chronological report programs to the frozen words of
one returned family. An arbitrary subtotal claim may be read by the sparse
continuation of each successfully reported row. -/
theorem ReturnedCandidateReports.paths {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns}
    (actual : ReturnedCandidateReports N t cell recv size raw site origin state siteID edgeID portID F
      original live host hdr body factors bank (b:=b) (gap:=gap) slot
      (ep:=ep) (em:=em) (er:=er) (out:=out) counts (outputs:=outputs) (x:=x) q) :
    ∃ program : Fin (R+1) → OpenSuffix.Inputs,
      OpenSuffix.ControlFamily program ep em er out ((source).pins q) ∧
      ((source).pins q → ∀ u, ∃ data : LocalReportData (ep u) (em u) (er u) (out u),
        SameReportCells data.cells ((source).cells q u)) :=
  candidate_report_family N t cell recv size raw site origin state siteID edgeID portID F original live host hdr body
    factors bank slot counts q actual.old actual.pin actual.subtotal actual.literal actual.address actual.descFit
    actual.paramFit actual.range actual.declared actual.opened actual.space actual.image actual.net actual.codes actual.widths
    actual.place actual.low actual.reserve actual.rest actual.fit actual.words actual.allocation actual.charge actual.supp
    actual.marked actual.uses actual.siteWidth actual.bodyFit actual.endFit actual.sourceRoom actual.returned

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
