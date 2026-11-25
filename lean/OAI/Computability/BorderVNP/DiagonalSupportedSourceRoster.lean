import OAI.Computability.BorderVNP.DiagonalRoutedReportCutDecoder
import OAI.Computability.BorderVNP.DiagonalRoutedIssuedInputs
import OAI.Computability.BorderVNP.DiagonalPrefixFinishRun
import OAI.Computability.BorderVNP.DiagonalProducedRoster

/-! # The real sparse roster from the bare routed tuple on a supported team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM CellMacro.Generator CompactMachine ScheduleClock BorderVNP.Cube

/-- Public operand words, fragment publication memory, and built argument
memory on exactly the two recorded sparse preparation visits. -/
noncomputable def argumentRosterCut {n w axes b h K letters : ℕ} {gen : Fragment IO}
    {id : TableEntry axes b h K letters → ℕ} (M : PinStart gen n w) (p : M.Prefix id) :
    (Arg → Word w) × Memory w × Memory w :=
  let visit := M.visited p
  let parts := (argumentVisitsEquiv M.pub (install gen n M.routines) visit.reports.val.2.1 visit.reports.val.2.2).symm
    visit.arguments
  (M.pub,parts.1.val.2.2,parts.2.1.val.2.2)

end RoutingISA.Evaluator.PinStart

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine Routing JointHeader
open CellMacro.Generator BorderVNP.Cube

variable {R r t d link inner n w reserve axes groups cap dim tally box lanes selectors symbols : ℕ}
    {Edge Hist : Type} (gen : Fragment IO) (id : TableEntry axes box lanes selectors symbols → ℕ)
    (G : Wiring R r t d link inner n Edge) (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (pin : Fin d → Bool) (L : WireLayout (R+1) r link)
    (headerWidth : L.header=PositiveFields.width reserve axes groups cap (R+1) dim tally)
    (code : Hist ↪ (Fin reserve → Bool))
    (args : Fin (R+1) → UnitAddresses) (fixed : Block (R+1)) (hw : 0<w)
    (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart gen G pub reg args pin x.val u)

local notation "Fields" => PositiveFields reserve axes groups cap (R+1) dim tally
local notation3 (prettyPrint := false) "U" => fun x u => (B x u).start
local notation "mac" => TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n)
local notation "active" => PinStart.preCallSupport U id
local notation3 (prettyPrint := false) "ib" => fun u => (args u).ibase
local notation3 (prettyPrint := false) "hb" => fun u => (args u).hbase
local notation3 (prettyPrint := false) "sb" => fun u => (args u).starbase
local notation "guess" => (fun (_ : {ext // PositiveExterior G args pin w ext}) (_ : Fin (R+1)) => rfl)


open RoutingISA.Evaluator.ScheduleClock DiagonalTallyCellReports _root_.OAI.Computability.BorderVNP.Cube.Physical.NativeLedger

variable (decoder : PreparedHistoryDecoder gen id G pub reg pin L headerWidth code args fixed hw size base fit B)
    (limit burst : ℕ) (room : TeamScales.width n (1/2) ≤ burst)
    (next : ∀ (y : {ext // PositiveExterior G args pin w ext ∧ PinStart.preCallSupport
      (fun x u => (B x u).start) id ext}) (u : Fin (R+1)), let node := B ⟨y.val,y.property.1⟩ u
      PositiveContinuation id gen n (pub u) (TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n))
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

set_option maxHeartbeats 500000 in
/-- The funded bare input and the supported team have exactly the same
public word bank, fragment rows RAM and sparse-call input RAM. -/
theorem PreparedHistoryDecoder.supported_sparseCut :
    ((T (activePrefix).1 u).start.argumentRosterCut ((activePrefix).2 u)) =
      (B (bare).1 u).start.argumentRosterCut ((bare).2 u) := by
  obtain ⟨i,h,v,c,reports⟩ := f
  let observe (z : Σ M : PinStart gen n w, M.Prefix id) := z.1.argumentRosterCut z.2
  exact congrArg observe (PreparedHistoryDecoder.supported_restored_pair gen id G pub reg pin L headerWidth
    code args fixed hw size base fit B decoder limit burst room next Route Report routed i h v c reports u)

set_option maxHeartbeats 500000 in
/-- Transport the funded launcher's actual source on its post-builder RAM
with the same rows, placement, geometry and supplemental records. The
target is precisely the `production` field of the positive finish. -/
theorem PreparedHistoryDecoder.supported_producedRoster (sa : SignedTaskArena.Layout) (rows : CellControlRows.Layout)
    {Site : Type} (placed : ℕ → CellPacket.Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record) :
    let orig := (B (bare).1 u).start.argumentRosterCut ((bare).2 u)
    let st := T (activePrefix).1 u
    let pr := (activePrefix).2 u
    let v := prefixVisits st pr
    let parts := (argumentVisitsEquiv st.pub (install gen n st.routines) v.reports.val.2.1 v.reports.val.2.2).symm v.arguments
    (∃ src : SparseCallInput orig.1 orig.2.2, ProducedRoster sa rows (readings orig.2.1) placed geom extra src) →
      ∃ src : SparseCallInput st.pub parts.2.1.val.2.2,
        ProducedRoster sa rows (readings parts.1.val.2.2) placed geom extra src := by
  let isProduced (s : (Arg → Word w) × Memory w × Memory w) :=
    ∃ src : SparseCallInput s.1 s.2.2, ProducedRoster sa rows (readings s.2.1) placed geom extra src
  exact (congrArg isProduced (PreparedHistoryDecoder.supported_sparseCut gen id G pub reg pin L headerWidth code
    args fixed hw size base fit B decoder limit burst room next routed f u)).mpr

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
