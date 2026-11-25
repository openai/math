import OAI.Computability.BorderVNP.DiagonalSupportedSourceRoster
import OAI.Computability.BorderVNP.DiagonalFundedRosterOnVisits

/-! # The funded native roster on a restored supported prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine Routing JointHeader
open CellMacro.Generator BorderVNP.Cube

variable {R r t d link inner n w reserve axes groups cap dim tally box lanes selectors symbols : ℕ}
    {Edge Hist : Type} (id : TableEntry axes box lanes selectors symbols → ℕ)
    (G : Wiring R r t d link inner n Edge) (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (pin : Fin d → Bool) (L : WireLayout (R+1) r link)
    (headerWidth : L.header=PositiveFields.width reserve axes groups cap (R+1) dim tally)
    (code : Hist ↪ (Fin reserve → Bool))
    (args : Fin (R+1) → UnitAddresses) (fixed : Block (R+1)) (hw : 0<w)
    (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G pub reg args pin x.val u)

local notation "Fields" => PositiveFields reserve axes groups cap (R+1) dim tally
local notation3 (prettyPrint := false) "U" => fun x u => (B x u).start
local notation "mac" => TeamSiteEvents.macros (w:=w) (siteLibrary SparseExterior.driver) (nativeClock n)
local notation "active" => PinStart.preCallSupport U id
local notation3 (prettyPrint := false) "ib" => fun u => (args u).ibase
local notation3 (prettyPrint := false) "hb" => fun u => (args u).hbase
local notation3 (prettyPrint := false) "sb" => fun u => (args u).starbase
local notation "guess" => (fun (_ : {ext // PositiveExterior G args pin w ext}) (_ : Fin (R+1)) => rfl)


open RoutingISA.Evaluator.ScheduleClock DiagonalTallyCellReports _root_.OAI.Computability.BorderVNP.Cube.Physical.NativeLedger

variable (decoder : PreparedHistoryDecoder SparseExterior.driver id G pub reg pin L headerWidth code args fixed hw size base fit B)
    (limit burst : ℕ) (room : TeamScales.width n (1/2) ≤ burst)
    (next : ∀ (y : {ext // PositiveExterior G args pin w ext ∧ PinStart.preCallSupport
      (fun x u => (B x u).start) id ext}) (u : Fin (R+1)), let node := B ⟨y.val,y.property.1⟩ u
      PositiveContinuation id SparseExterior.driver n (pub u) (TeamSiteEvents.macros (w:=w) (siteLibrary SparseExterior.driver) (nativeClock n))
        node.start.bank node.memory node.pins node.used limit)
    {Route : Hist → Type} {Report : (Fin d → Bool) → (q : Hist) → Route q → Type}
    (routed : ∀ (i : Fin d → Bool) (q : Hist) (claim : Fin ((R+1)*dim*tally) → Bool),
      (Σ c : Physical.Broadcast axes groups cap,
        ParsedPreCall G args pin L fixed hw size base fit headerWidth (fun x u => (B x u).start)
          (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) (fun _ _ => rfl)
          id i ⟨code q,c,claim⟩) ≃ Σ v : Route q,Report i q v)
    (f : PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool) Route Report) (u : Fin (R+1))

local notation3 (prettyPrint := false) "T" => supportedTeam id B limit burst room next
local notation3 (prettyPrint := false) "activePrefix" => (decoder.supported limit burst room next Route Report routed).val.symm f
local notation3 (prettyPrint := false) "bare" => routedBareTuple routed f

open RoutingISA.FragmentRows CellSparse CellSparse.Packet CellPacket.Supplement SignedTaskArena

local notation3 (prettyPrint := false) "starts" => fun j => (B (bare).1 j).start
local notation3 (prettyPrint := false) "nativeCut" => (B (bare).1 u).start.argumentRosterCut ((bare).2 u)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 6500 in
/-- The original funded fragment and its chosen patch also issue the call
on the supported inverse of this very source, report tape and subtotal. -/
theorem PreparedHistoryDecoder.supported_fundedRoster
    {sa : SignedTaskArena.Layout} {fr : FragmentRows.Layout} {orig : Memory w}
    {fit₀ : fr.Fits w (readings orig)} {cells : sa.fragments.cells=fr.cells}
    (e : SparseEmission sa fr orig fit₀ cells) {team frame offsets ctl live ports : ℕ}
    {data : ℕ → ℕ → Bool} {Site : Type}
    (patch : SparsePatch Site (sa.controlRows team frame offsets ctl live ports) (readings e.output))
    (row : (i : Fin ((sa.controlRows team frame offsets ctl live ports).toLayout.before (readings e.output) sa.cube.cells)) →
      SparseCell sa fr orig data i.val) {description : ℕ}
    (launch : SparseEmission.NativeInputAt id starts ((bare).2 u) e patch row description)
    (atMemory : e.output=(nativeCut).2.1) :
    let st := T (activePrefix).1 u
    let pr := (activePrefix).2 u
    let vis := prefixVisits st pr
    let parts := (argumentVisitsEquiv st.pub (install SparseExterior.driver n st.routines)
      vis.reports.val.2.1 vis.reports.val.2.2).symm vis.arguments
    ∃ src : SparseCallInput st.pub parts.2.1.val.2.2,
      ProducedRoster sa (sa.controlRows team frame offsets ctl live ports) (readings parts.1.val.2.2)
        patch.placed patch.geometry patch.extra src := by
  apply PreparedHistoryDecoder.supported_producedRoster SparseExterior.driver id G pub reg pin L headerWidth code args
    fixed hw size base fit B decoder limit burst room next routed f u sa (sa.controlRows team frame offsets ctl live ports)
    patch.placed patch.geometry patch.extra
  exact ⟨launch.native.source,launch.rosterOnVisits id starts ((bare).2 u) e patch row atMemory⟩

set_option maxHeartbeats 800000 in
set_option maxRecDepth 6500 in
/-- The same physical patch supplies the positive team's control rows,
including its own frame read from public operand zero on that prefix. -/
theorem PreparedHistoryDecoder.supported_fundedPatch
    {sa : SignedTaskArena.Layout} {fr : FragmentRows.Layout} {orig : Memory w}
    {fit₀ : fr.Fits w (readings orig)} {cells : sa.fragments.cells=fr.cells}
    (e : SparseEmission sa fr orig fit₀ cells) {team offsets ctl live ports : ℕ}
    {data : ℕ → ℕ → Bool} {Site : Type}
    (patch : SparsePatch Site (sa.controlRows team ((nativeCut).1 0).val offsets ctl live ports) (readings e.output))
    (row : (i : Fin ((sa.controlRows team ((nativeCut).1 0).val offsets ctl live ports).toLayout.before (readings e.output) sa.cube.cells)) →
      SparseCell sa fr orig data i.val) {description : ℕ}
    (launch : SparseEmission.NativeInputAt id starts ((bare).2 u) e patch row description)
    (atMemory : e.output=(nativeCut).2.1) :
    let st := T (activePrefix).1 u
    let pr := (activePrefix).2 u
    let vis := prefixVisits st pr
    let parts := (argumentVisitsEquiv st.pub (install SparseExterior.driver n st.routines)
      vis.reports.val.2.1 vis.reports.val.2.2).symm vis.arguments
    ∃ (Orig : Type) (placed : ℕ → CellPacket.Placed Orig) (geometry : ℕ → ℕ) (extras : ℕ → List CellSparse.Record)
      (src : SparseCallInput st.pub parts.2.1.val.2.2),
      ProducedRoster sa (sa.controlRows team (st.pub 0).val offsets ctl live ports) (readings parts.1.val.2.2)
        placed geometry extras src := by
  intro st pr vis parts
  have same := PreparedHistoryDecoder.supported_sparseCut SparseExterior.driver id G pub reg pin L headerWidth
    code args fixed hw size base fit B decoder limit burst room next routed f u
  have frame : (st.pub 0).val=((nativeCut).1 0).val := congrArg (fun a => (a.1 0).val) same
  obtain ⟨src,issued⟩ := PreparedHistoryDecoder.supported_fundedRoster id G pub reg pin L headerWidth code
    args fixed hw size base fit B decoder limit burst room next routed f u e patch row launch atMemory
  refine ⟨Site,patch.placed,patch.geometry,patch.extra,src,?_⟩
  exact (congrArg (fun base => ProducedRoster sa (sa.controlRows team base offsets ctl live ports)
    (readings parts.1.val.2.2) patch.placed patch.geometry patch.extra src) frame).mpr issued

variable {id G pub reg pin L headerWidth code args fixed hw size base fit B}

local notation3 (prettyPrint := false) "transfer" =>
  @PreparedHistoryDecoder.supported_fundedPatch R r t d link inner n w reserve axes groups cap dim tally box lanes selectors symbols
    Edge Hist id G pub reg pin L headerWidth code args fixed hw size base fit B decoder limit burst room next Route Report routed

/-- The decoded program fixes its own public and private operands when
applying the funded patch observation to the original proposal. -/
theorem PreparedHistoryDecoder.fundedRouteObserver : type_of% (transfer) := transfer

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
