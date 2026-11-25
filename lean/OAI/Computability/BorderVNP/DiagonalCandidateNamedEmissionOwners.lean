import OAI.Computability.BorderVNP.DiagonalCandidatePublishedOwners

/-! # Receiving owners at the group labels of the original packet -/

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

/-- Read an original packet's group label at the native chosen coordinate. The
greedy owner table is the one used by this report's physical return. -/
theorem CandidateReportPublication.proposedOwnersAtLabels
    (K : CandidateReportPublication N t cell recv size raw site origin siteID portID F original live
      (outputs:=outputs) (x:=x) (b:=b) (gap:=gap))
    {q : NativeAssignments.Routed (blocks:=t.cube.header.blocks) (K:=t.cube.K) (h:=t.cube.h)
      (b:=t.cube.b) (s:=t.cube.s) owns}
    (opening : CandidateReportOpening N t cell recv size raw site origin state host hdr body factors slot
      (ep:=ep) (em:=em) (er:=er) (out:=out) (b:=b) q)
    (ownerAt : ∀ c : Fin t.cube.cells, routedOwnerWord t.cube owns label q c.val=(owner c.val).val)
    {named : Fin t.cube.cells → Label (t.cube.n+1) t.cube.header.d}
    (names : named=label)
    (u : Fin (R+1)) (advance : Returns controls (ep u) (em u) (er u) (out u))
    (report : Returns prepareCellReports (ep u) (em u) advance.val.2.1 advance.val.2.2)
    {L : ReportLayout} {cs : List (ReportCell L)} {cursor : ReportCursor} {banks : CellBanks.Layout}
    {description : ℕ} (seed : PreparedReportInput (ep u) advance.val.2.2 cs cursor description)
    (alloc : ReportAllocation t.before t.after banks L cs cursor) (bankAt : banks.bankStart=t.cube.cellBank)
    {fit : (FragmentRows.Layout.fromFrame (ep u 0).val (readings report.val.2.2)).Fits w (readings report.val.2.2)}
    {cc : t.fragments.cells=(FragmentRows.Layout.fromFrame (ep u 0).val (readings report.val.2.2)).cells}
    (emission : FragmentRows.SparseEmission t (FragmentRows.Layout.fromFrame (ep u 0).val
      (readings report.val.2.2)) report.val.2.2 fit cc) :
    ∀ c : Fin t.cube.cells,
      (t.controlRows u.val (ep u 0).val (tables(u)).ends (ctl(u)) (tables(u)).livePairs (d.teams*d.sites)).owner
        (readings emission.output) c.val=(owns q.1 (named c (chosen t.cube.b t.cube.s q.1))).val := by
  subst named
  exact K.proposedOwnersOnReturn opening ownerAt u advance report seed alloc bankAt emission

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
