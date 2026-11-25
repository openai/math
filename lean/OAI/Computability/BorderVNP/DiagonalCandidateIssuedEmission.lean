import OAI.Computability.BorderVNP.DiagonalCandidateFragmentRoom
import OAI.Computability.BorderVNP.DiagonalCandidateReportFamily
import OAI.Computability.BorderVNP.DiagonalIssuedEmissionAtFrame

/-! # The actual fragment emitter recovered from the checked writer and report -/

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

/-- The reconstructed public candidate and its own report determine the
fragment emitter on the original joint prefix, even for arbitrary guessed
report bits. Its registers and RAM are the states consumed by the first
native argument return. -/
theorem ReturnedCandidateReports.issuedEmissionOnPrefix
    {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns}
    (actual : ReturnedCandidateReports N t cell recv size raw site origin state siteID edgeID portID F
      original live host hdr body factors bank (b:=b) (gap:=gap) slot
      (ep:=ep) (em:=em) (er:=er) (out:=out) counts (outputs:=outputs) (x:=x) q)
    (pubAt : (ep u 0).val=(core 0).val) (owned : out u=(V).owned.val.2.2)
    (assigned : host=cell ∘ original) (fresh : (site u).fresh=up) (destination : origin u=dst)
    {suffix : ℕ} (complete : TerminalCells.signedGridOutputCount t.cube.cables t.cube.cells d.entries
      (d.teams*d.sites) 37 suffix ≤ (site u).outputs)
    (caps : Header (base(u)) (origin u) t.cube.cables t.cube.cells d.entries (readings (site u).geometry))
    {l : ReportLayout} {cs : List (ReportCell l)} {cur : ReportCursor} {bl : CellBanks.Layout} {description : ℕ}
    (seed : PreparedReportInput core (V).controls.val.2.2 cs cur description)
    (alloc : ReportAllocation t.before t.after bl l cs cur) (bankAt : bl.bankStart=t.cube.cellBank)
    (arena : StartupArena) {res axes groups cap width inputs guesses gates : ℕ}
    (bounds : t.FinishAddresses arena (ctl(u)) res axes groups cap width w inputs guesses gates)
    (head : (core 0).val=arena.frame) :
    IssuedReportFrame t core mp (tables(u)).ends (ctl(u)) dataRows ∧
    ∃ (fit : (sc).Fits w (readings mp)) (cells : t.fragments.cells=(sc).cells) (e : FragmentRows.SparseEmission t sc mp fit cells),
      e.bank=(steps).1.val.2.1 ∧ e.output=(steps).1.val.2.2 ∧ FragmentRows.SparseGeometry t sc (tables(u)).ends (ctl(u)) ∧
      ∀ i : Fin 37, readings mp (ctl(u)+i.val)=t.controls i.val := by
  have loaded := (site u).input
  rw [actual.literal u] at loaded
  have native := (site u).receipt.native_entry t (site u).placement (f u) (actual.old u) (origin u)
    t.cube.cables t.cube.cells actual.pin actual.subtotal (site u).fresh (site u).gates (site u).outputs
    (site u).width (site u).off (site u).ell (site u).control (site u).profile (site u).claims
    (site u).pad raw (site u).actual loaded
  rw [actual.address u] at native
  have opened := actual.opened.2 u
  rw [assigned,pubAt,owned] at opened
  have placed := actual.place u
  rw [(site u).origin] at placed caps native opened
  have reserve : t.cube.header.header=Allocation.stop up (site u).profile.length (site u).gates (site u).outputs (site u).width w := by
    rw [←fresh]
    exact congrArg CubeHeaderInstall.Inputs.header (site u).input.geometry
  have report := (site u).issuedFragmentRoom t (fun v => Site.size (state v)) siteID edgeID portID F
    (prof:=(site u).profile.length) (gates:=(site u).gates) (words:=(site u).outputs) (width:=(site u).width)
    (tail:=suffix) (gap:=gap) (bankBits:=b) (original:=original) (live:=live)
    u (V).controls (V).reports hdr (actual.net u) actual.codes actual.widths actual.allocation
    (by rw [←destination]; exact actual.image u)
    (by rw [←destination]; exact placed)
    (by rw [←destination]; exact caps)
    bounds.endFit reserve complete
    (by rw [←destination]; exact native)
    (by rw [←destination]; exact opened) seed alloc bankAt
  rw [←destination] at report
  have rowsFit := (Nat.le_add_right dataRows (t.cube.header.d.choose 2)).trans (site u).input.records
  refine ⟨report,?_⟩
  exact PinStart.issuedEmissionAtFrame t U active u (tables(u)).ends (ctl(u)) dataRows arena bounds head report rowsFit


/-- The host word on this very owned return is the original receiving owner
recorded by the matching site's public scheduler. -/
theorem ReturnedCandidateReports.fundedOwnerWord
    {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns}
    (actual : ReturnedCandidateReports N t cell recv size raw (site) origin state siteID edgeID portID F
      original live host hdr body factors bank (b:=b) (gap:=gap) slot
      (ep:=ep) (em:=em) (er:=er) (out:=out) counts (outputs:=outputs) (x:=x) q)
    (owned : out u=(V).owned.val.2.2) :
    ∀ c : Fin t.cube.cells, readings (V).owned.val.2.2 (t.cube.hostDirectory+2*c.val)=(owner c.val).val := by
  have loaded := (site u).input
  rw [actual.literal u] at loaded
  have entry := (site u).receipt.native_entry t (site u).placement (f u) (actual.old u) (origin u)
    t.cube.cables t.cube.cells actual.pin actual.subtotal (site u).fresh (site u).gates (site u).outputs
    (site u).width (site u).off (site u).ell (site u).control (site u).profile (site u).claims
    (site u).pad raw (site u).actual loaded
  have kept := (actual.opened.2 u).retained
  intro c
  rw [←owned]
  exact (t.retainedOwner entry ⟨kept.primary,fun i hi s₁ s₂ =>
    (kept.lower i hi s₁ s₂).trans (entry.low i hi),kept.tables⟩ c).trans
      (congrArg Fin.val ((site u).receipt.owners c))

variable {N t cell recv size raw site origin state siteID edgeID portID F original live host hdr body factors bank slot counts}

/-- The reporter's own directory publication, before its native ownership
and report scans. The indexed certificate fixes which site published it. -/
noncomputable abbrev ReturnedCandidateReports.sourcePublication
    {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owns}
    (_ : ReturnedCandidateReports N t cell recv size raw site origin state siteID edgeID portID F
      original live host hdr body factors bank (b:=b) (gap:=gap) slot
      (ep:=ep) (em:=em) (er:=er) (out:=out) counts (outputs:=outputs) (x:=x) q)
    (team : Fin (R+1)) : Memory w := (site team).published.val.2.2

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
