import OAI.Computability.BorderVNP.DiagonalReplayReportStages
import OAI.Computability.BorderVNP.DiagonalCandidateFragmentRoom
import OAI.Computability.BorderVNP.PackedTerminalSignedGridEmitterCost

/-! # The staged frozen source of a candidate fragment directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing _root_.OAI.Computability.BorderVNP.Cube Physical MeanChoice GroupWeights LabelIndex Tally
open TeamContraction JointHeader LocalRow Transmission VPVNP.BurstRAM PackedHistoryCircuit
open Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.RoutingOutputs
open VPVNP.VerifierNetwork Packing.Inherited Packing.BottomReports DiagonalTallyCellReports
open DiagonalTallyAllocation ReportDirectory DiagonalResidueRAM FiniteEvaluator GeometryFrameEncoding
open CellMacro.Generator
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

/-- On one candidate, its staged publication and capacity give the physical
fragment directory produced by every returned control and report. The actual
issued gate table fixes all four geometric inputs. -/
theorem CandidateReportPublication.issuedFrameOnReturn
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
    ScheduleClock.IssuedReportFrame t (ep u) report.val.2.2 (tables(u)).ends (ctl(u)) (d.directory pp lp).length := by
  have input := (site u).input
  rw [K.literal u] at input
  have entry := (site u).receipt.native_entry t (site u).placement (f u) (K.old u) (origin u) t.cube.cables t.cube.cells
    K.pin K.subtotal (site u).fresh (site u).gates (site u).outputs (site u).width (site u).off (site u).ell
    (site u).control (site u).profile (site u).claims (site u).pad raw (site u).actual input
  have saved := opening.2 u
  have placed := K.place u
  have image := K.image u
  rw [(site u).origin] at geomHeader placed saved entry
  rw [K.address u] at entry
  rw [first] at located
  have reserve : t.cube.header.header=GeometryAdvice.Allocation.stop (receiving+7*d.candidates)
      (site u).profile.length (site u).gates (site u).outputs (site u).width w := by
    rw [←first]
    exact congrArg (fun h => h.header) (site u).input.geometry
  rw [located] at image placed saved entry geomHeader ⊢
  exact (site u).issuedFragmentRoom t (fun v => Site.size (state v)) siteID edgeID portID F u advance report
    (tail:=0) hdr (C.net u) C.codes C.widths C.allocation image placed geomHeader C.endFit reserve sized
    entry saved seed alloc baseBank

/-- The compacted roster and the physical cell and cable dimensions of the
candidate's returned sparse frame. -/
theorem CandidateReportPublication.fragmentOnReturn
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
    ∃ fr : ScheduleClock.FragmentDirectoryInput (ep u) report.val.2.2, fr.layout.count=(d.directory pp lp).length ∧
      t.fragments.cells=fr.layout.cells ∧ fr.layout.host.count=t.cube.cables ∧
      FragmentRows.SparseGeometry t fr.layout (tables(u)).ends (ctl(u)) := by
  obtain ⟨fr,_,count,_,cells,cables,_,_,geo⟩ :=
    K.issuedFrameOnReturn C opening u first located sized geomHeader advance report seed alloc baseBank
  exact ⟨fr,count,cells,cables,geo⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
