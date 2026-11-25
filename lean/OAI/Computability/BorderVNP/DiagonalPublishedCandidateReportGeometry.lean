import OAI.Computability.BorderVNP.DiagonalPublishedCandidateFragment
import OAI.Computability.BorderVNP.DiagonalReturnedFragmentGeometry

/-! # Original wire and cell records at a candidate's returned report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing _root_.OAI.Computability.BorderVNP.Cube Physical MeanChoice GroupWeights LabelIndex Tally
open TeamContraction JointHeader LocalRow Transmission VPVNP.BurstRAM PackedHistoryCircuit
open Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.RoutingOutputs
open VPVNP.VerifierNetwork Packing.Inherited Packing.BottomReports DiagonalTallyCellReports
open DiagonalTallyAllocation ReportDirectory DiagonalResidueRAM FiniteEvaluator GeometryFrameEncoding
open CellMacro.Generator Diagonal.ExternalSew.Fragments
open scoped Classical

set_option maxRecDepth 6100
set_option maxHeartbeats 1200000

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
local notation3 (prettyPrint := false) "report(" u ")" => reportLayout t.before t.after (base(u)) (ctl(u)) t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop

variable {ep : Fin (R+1) → Arg → Word w} {em : Fin (R+1) → TeamOpcode.Macros w 8}
    {er : Fin (R+1) → Bank w} {out : Fin (R+1) → Memory w}

variable {N t cell recv size raw site origin state siteID edgeID portID F original live host hdr body factors bank slot}

/-- The physical signed report preserves the original cable rows and every
cell's supply count and receiving-bank pointer, including on a rejected proposal. -/
theorem CandidateReportPublication.reportGeometry
    (K : CandidateReportPublication N t cell recv size raw site origin siteID portID F original live
      (outputs:=outputs) (x:=x) (b:=b) (gap:=gap))
    (C : CandidateReportCapacity N t cell recv size raw site origin state siteID edgeID portID F
      host hdr body factors bank slot (x:=x) (gap:=gap))
    {q : NativeAssignments.Routed (blocks:=t.cube.header.blocks) (K:=t.cube.K) (h:=t.cube.h)
      (b:=t.cube.b) (s:=t.cube.s) owns}
    (opening : CandidateReportOpening N t cell recv size raw site origin state host hdr body factors slot
      (ep:=ep) (em:=em) (er:=er) (out:=out) (b:=b) q)
    (u : Fin (R+1))
    (located : origin u=GeometryAdvice.Allocation.dest (site u).fresh (site u).profile.length
      (site u).gates (site u).outputs (site u).width)
    (sized : TerminalCells.signedGridOutputCount t.cube.cables t.cube.cells d.entries (d.teams*d.sites) 37 0 ≤ (site u).outputs)
    (geomHeader : Header (base(u)) (origin u) t.cube.cables t.cube.cells d.entries (readings (site u).geometry))
    (advance : Returns controls (ep u) (em u) (er u) (out u))
    (report : Returns prepareCellReports (ep u) (em u) advance.val.2.1 advance.val.2.2)
    {L : ReportLayout} {cells : List (ReportCell L)} {cursor : ReportCursor} {banks : CellBanks.Layout} {description : ℕ}
    (seed : PreparedReportInput (ep u) advance.val.2.2 cells cursor description)
    (alloc : ReportAllocation t.before t.after banks L cells cursor) (baseBank : banks.bankStart=t.cube.cellBank) :
    let ram := readings report.val.2.2
    let fields := FragmentRows.Layout.fromFrame (ep u 0).val ram
    SignedTaskArena.ReportWords t (ep u 0).val (readings (site u).published.val.2.2)
      (readings (site u).receipt.history.dataInput) ram true ∧
      CableRows N cell edgeID portID fields.host ram ∧
      (∀ c : Fin t.cube.cells, ram (fields.supplied+c.val)=suppliedSize N cell c) ∧
      ∀ c : Fin t.cube.cells, ram (fields.host.cells+2*c.val+1)=t.cube.cellBank+c.val*t.cube.cellStride := by
  let v := site u
  have pinned := v.input
  rw [K.literal u] at pinned
  have native := v.receipt.native_entry t v.placement (f u) (K.old u) (origin u) t.cube.cables t.cube.cells
    K.pin K.subtotal v.fresh v.gates v.outputs v.width v.off v.ell v.control v.profile v.claims v.pad raw v.actual pinned
  have ctl := opening.2 u
  let init := readings v.published.val.2.2
  let written := readings v.receipt.history.dataInput
  have keep : CubeAllocation.HostRetention t.cube (base(u)) init written (readings (out u)) :=
    ⟨ctl.retained.primary,fun j hj h₀ h₁ => (ctl.retained.lower j hj h₀ h₁).trans (native.low j hj),ctl.retained.tables⟩
  have actual : readings (Packing.Directory.ISA.publish v.middle (base(u)) receiving (d.directory pp lp))=init := by
    dsimp only [init]
    rw [v.actual]
  have retained := t.signed_report_words (team:=u.val) (offsets:=(tables(u)).ends) (ctl:=ctl(u))
    (live:=(tables(u)).livePairs) (ports:=d.teams*d.sites) (b:=b) host hdr advance report seed
    (ctl.frame.symm ▸ keep) (by simpa only [ctl.frame] using ctl.ready)
    (by simpa only [ctl.frame] using ctl.placement) alloc baseBank
  have keepOriginal : SignedTaskArena.ReportWords t (base(u))
      (readings (Packing.Directory.ISA.publish v.middle (base(u)) receiving (d.directory pp lp))) written
      (readings report.val.2.2) true := by
    rw [actual,←ctl.frame]
    exact retained
  have visible := published_routing_header pp lp (K.place u) geomHeader (K.low u) (K.reserve u)
  have hostPtr := (keep.open_frame 72 (by decide)).symm.trans ctl.placement.pointer
  have stop : origin u+5*t.cube.cables+t.cube.cells≤t.cube.header.header := by
    have cap := congrArg (fun h => h.header) v.input.geometry
    change t.cube.header.header=GeometryAdvice.Allocation.stop v.fresh v.profile.length v.gates v.outputs v.width w at cap
    rw [cap,located]
    dsimp only [v,GeometryAdvice.Allocation.stop,GeometryAdvice.Allocation.packed,GeometryAdvice.Allocation.dense]
    dsimp only [TerminalCells.signedGridOutputCount,Packing.RoutingOutputs.count] at sized
    omega
  obtain ⟨scheduled,_,assignment⟩ := native.image
  have received := keepOriginal.returnedGeometry t N cell (fun v => Site.size (state v)) siteID edgeID portID F d pp lp
    (C.net u) C.codes C.widths (K.image u) (K.place u) (K.low u) (K.reserve u) stop visible
    (by rw [actual]; exact hostPtr) assignment
  refine ⟨retained,?_⟩
  rw [ctl.frame]
  exact received

/-- The same returned memory supplies both the fragment opened by the
native processor and the surviving wire, supply, and bank tables. -/
theorem CandidateReportPublication.reportFrameGeometry
    (K : CandidateReportPublication N t cell recv size raw site origin siteID portID F original live
      (outputs:=outputs) (x:=x) (b:=b) (gap:=gap))
    (C : CandidateReportCapacity N t cell recv size raw site origin state siteID edgeID portID F
      host hdr body factors bank slot (x:=x) (gap:=gap))
    {q : NativeAssignments.Routed (blocks:=t.cube.header.blocks) (K:=t.cube.K) (h:=t.cube.h)
      (b:=t.cube.b) (s:=t.cube.s) owns}
    (opening : CandidateReportOpening N t cell recv size raw site origin state host hdr body factors slot
      (ep:=ep) (em:=em) (er:=er) (out:=out) (b:=b) q)
    (u : Fin (R+1))
    (first : (site u).fresh=receiving+7*d.candidates)
    (located : origin u=GeometryAdvice.Allocation.dest (site u).fresh (site u).profile.length
      (site u).gates (site u).outputs (site u).width)
    (sized : TerminalCells.signedGridOutputCount t.cube.cables t.cube.cells d.entries (d.teams*d.sites) 37 0 ≤ (site u).outputs)
    (geomHeader : Header (base(u)) (origin u) t.cube.cables t.cube.cells d.entries (readings (site u).geometry))
    (advance : Returns controls (ep u) (em u) (er u) (out u))
    (report : Returns prepareCellReports (ep u) (em u) advance.val.2.1 advance.val.2.2)
    {L : ReportLayout} {cells : List (ReportCell L)} {cursor : ReportCursor} {banks : CellBanks.Layout} {description : ℕ}
    (seed : PreparedReportInput (ep u) advance.val.2.2 cells cursor description)
    (alloc : ReportAllocation t.before t.after banks L cells cursor) (baseBank : banks.bankStart=t.cube.cellBank) :
    let ram := readings report.val.2.2
    let fields := FragmentRows.Layout.fromFrame (ep u 0).val ram
    ScheduleClock.IssuedReportFrame t (ep u) report.val.2.2 (tables(u)).ends (ctl(u)) (d.directory pp lp).length ∧
    SignedTaskArena.ReportWords t (ep u 0).val (readings (site u).published.val.2.2)
      (readings (site u).receipt.history.dataInput) ram true ∧
      CableRows N cell edgeID portID fields.host ram ∧
      (∀ c : Fin t.cube.cells, ram (fields.supplied+c.val)=suppliedSize N cell c) ∧
      ∀ c : Fin t.cube.cells, ram (fields.host.cells+2*c.val+1)=t.cube.cellBank+c.val*t.cube.cellStride :=
  ⟨K.issuedFrameOnReturn C opening u first located sized geomHeader advance report seed alloc baseBank,
    K.reportGeometry C opening u located sized geomHeader advance report seed alloc baseBank⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
