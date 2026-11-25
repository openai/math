import OAI.Computability.BorderVNP.DiagonalCandidateIssuedEmission
import OAI.Computability.BorderVNP.DiagonalReturnedFragmentGeometry

/-! # Network rows at the registered candidate's actual signed report return -/

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
variable {ep : Fin (R+1) → Arg → Word w} {em : Fin (R+1) → TeamOpcode.Macros w 8}
    {er : Fin (R+1) → Bank w} {out : Fin (R+1) → Memory w}
    (counts : Fin (R+1) → ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool)

open CompactMachine CellMacro.Generator TeamContraction.JointHeader TeamContraction.ProcessorSlots
open SignedTaskArena Physical.NativeAssignments GeometryAdvice Evaluator.ScheduleClock

set_option maxHeartbeats 2200000
set_option maxRecDepth 7000

variable {n : ℕ} (U : Fin (R+1) → PinStart SparseExterior.driver n w) (active : PinStart.JointPrefix t.id U)
    (u : Fin (R+1))

local notation3 (prettyPrint := false) "V" => PinStart.visits t.id U (active u)
local notation3 (prettyPrint := false) "mp" => (V).reports.val.2.2
local notation3 (prettyPrint := false) "core" => (U u).pub
local notation3 (prettyPrint := false) "code" => install SparseExterior.driver n (U u).routines
local notation3 (prettyPrint := false) "sc" => FragmentRows.Layout.fromFrame (core 0).val (readings mp)
local notation3 (prettyPrint := false) "steps" => (argumentVisitsEquiv core code (V).reports.val.2.1 mp).symm (V).arguments
local notation3 (prettyPrint := false) "up" => receiving+7*d.candidates
local notation3 (prettyPrint := false) "dst" => Allocation.dest up (site u).profile.length (site u).gates (site u).outputs (site u).width
local notation3 (prettyPrint := false) "dataRows" => (d.directory pp lp).length


open Diagonal.ExternalSew.Fragments

/-- Read the original cable rows, supplied widths and assigned bank pointers
through the candidate's actual directory publication and native report. -/
theorem ReturnedCandidateReports.registeredReportGeometry
    {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns}
    (actual : ReturnedCandidateReports N t cell recv size raw site origin state siteID edgeID portID F
      original live host hdr body factors bank (b:=b) (gap:=gap) slot
      (ep:=ep) (em:=em) (er:=er) (out:=out) counts (outputs:=outputs) (x:=x) q)
    (pubAt : (ep u 0).val=(core 0).val)
    (located : origin u=Allocation.dest (site u).fresh (site u).profile.length
      (site u).gates (site u).outputs (site u).width)
    {suffix : ℕ} (complete : TerminalCells.signedGridOutputCount t.cube.cables t.cube.cells d.entries
      (d.teams*d.sites) 37 suffix ≤ (site u).outputs)
    (caps : Header (base(u)) (origin u) t.cube.cables t.cube.cells d.entries (readings (site u).geometry))
    (words : SignedTaskArena.ReportWords t (core 0).val (readings (site u).published.val.2.2)
      (readings (site u).receipt.history.dataInput) (readings mp) true) :
    CableRows N cell edgeID portID (sc).host (readings mp) ∧
      (∀ c : Fin t.cube.cells, readings mp ((sc).supplied+c.val)=suppliedSize N cell c) ∧
      ∀ c : Fin t.cube.cells, readings mp ((sc).host.cells+2*c.val+1)=t.cube.cellBank+c.val*t.cube.cellStride := by
  let v := site u
  have entryInput := v.input
  rw [actual.literal u] at entryInput
  have entry := v.receipt.native_entry t v.placement (f u) (actual.old u) (origin u) t.cube.cables t.cube.cells
    actual.pin actual.subtotal v.fresh v.gates v.outputs v.width v.off v.ell v.control v.profile v.claims v.pad
    raw v.actual entryInput
  have opened := actual.opened.2 u
  have frameEq : base(u)=(core 0).val := opened.frame.symm.trans pubAt
  rw [←frameEq] at words ⊢
  let initial := readings v.published.val.2.2
  have kept : CubeAllocation.HostRetention t.cube (base(u)) initial (readings v.receipt.history.dataInput)
      (readings (out u)) := ⟨opened.retained.primary,fun j hj h₀ h₁ =>
        (opened.retained.lower j hj h₀ h₁).trans (entry.low j hj),opened.retained.tables⟩
  have publication : readings (Packing.Directory.ISA.publish v.middle (base(u)) receiving (d.directory pp lp))=initial := by
    dsimp only [initial]
    rw [v.actual]
  have retained : SignedTaskArena.ReportWords t (base(u))
      (readings (Packing.Directory.ISA.publish v.middle (base(u)) receiving (d.directory pp lp)))
      (readings v.receipt.history.dataInput) (readings mp) true := by
    rw [publication]
    exact words
  have header := published_routing_header pp lp (actual.place u) caps (actual.low u) (actual.reserve u)
  have hostPtr := (kept.open_frame 72 (by decide)).symm.trans opened.placement.pointer
  have stop : origin u+5*t.cube.cables+t.cube.cells≤t.cube.header.header := by
    have cap := congrArg (fun h => h.header) v.input.geometry
    change t.cube.header.header=Allocation.stop v.fresh v.profile.length v.gates v.outputs v.width w at cap
    rw [cap,located]
    dsimp only [v,Allocation.stop,Allocation.packed,Allocation.dense]
    dsimp only [TerminalCells.signedGridOutputCount,Packing.RoutingOutputs.count] at complete
    omega
  obtain ⟨_,_,assigned⟩ := entry.image
  exact retained.returnedGeometry t N cell (fun z => Site.size (state z)) siteID edgeID portID F d pp lp
    (actual.net u) actual.codes actual.widths (actual.image u) (actual.place u) (actual.low u)
    (actual.reserve u) stop header (by rw [publication]; exact hostPtr) assigned

/-- Specialize the registered writer's report-word receipt to the two opening
conditions on this candidate, at its original prefix and physical publication. -/
theorem ReturnedCandidateReports.registeredReportWordsAt
    {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns}
    (actual : ReturnedCandidateReports N t cell recv size raw site origin state siteID edgeID portID F
      original live host hdr body factors bank (b:=b) (gap:=gap) slot
      (ep:=ep) (em:=em) (er:=er) (out:=out) counts (outputs:=outputs) (x:=x) q)
    (pubAt : (ep u 0).val=(core 0).val)
    (owned : out u=(V).owned.val.2.2)
    {middle : Memory w} {initial baseAddress : ℕ} {rows : List Packing.Directory.Row}
    (head : (core 0).val=initial)
    (onSite : (site u).published.val.2.2=Packing.Directory.ISA.publish middle initial baseAddress rows)
    (read : OpenSuffix.Ready (t.openInputs u.val (core 0).val (tables(u)).ends (ctl(u)) (tables(u)).livePairs
        (d.teams*d.sites) d.entries b host hdr) (core 0).val (readings (V).owned.val.2.2) w →
      OpenSuffix.Placement (t.openInputs u.val (core 0).val (tables(u)).ends (ctl(u)) (tables(u)).livePairs
        (d.teams*d.sites) d.entries b host hdr) t.cube t.before (core 0).val (readings (V).owned.val.2.2) →
      SignedTaskArena.ReportWords t (core 0).val
        (readings (Packing.Directory.ISA.publish middle (core 0).val baseAddress rows))
        (readings (site u).receipt.history.dataInput) (readings mp) true) :
    SignedTaskArena.ReportWords t (core 0).val (readings (site u).published.val.2.2)
      (readings (site u).receipt.history.dataInput) (readings mp) true := by
  have opened := actual.opened.2 u
  rw [pubAt,owned] at opened
  have onPrefix := onSite.trans (congrArg (fun frame => Packing.Directory.ISA.publish middle frame baseAddress rows) head.symm)
  apply (congrArg (fun memory : Memory w => SignedTaskArena.ReportWords t (core 0).val (readings memory)
    (readings (site u).receipt.history.dataInput) (readings mp) true) onPrefix).mpr
  exact read (by simpa only [opened.frame] using opened.ready)
    (by simpa only [opened.frame] using opened.placement)

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
