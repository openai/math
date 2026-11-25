import OAI.Computability.BorderVNP.DiagonalRoutedBareOwnerHistory
import OAI.Computability.BorderVNP.DiagonalAdmittedReportCut

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # The assigned report on the literal bare decoder return -/

namespace TeamContraction.ProcessorSlots.BootedPinStart

open Cube.Physical RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine Routing JointHeader
open CellMacro.Generator BorderVNP.Cube

variable {R r t d link inner n w reserve dim tally : ℕ} {ar : CubeArena.Layout}
    {Edge Hist : Type} (gen : Fragment IO) (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (G : Wiring R r t d link inner n Edge) (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (pin : Fin d → Bool) (L : WireLayout (R+1) r link)
    (headerWidth : L.header=PositiveFields.width reserve ar.n ar.header.d (declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s) (R+1) dim tally)
    (code : Hist ↪ (Fin reserve → Bool))
    (args : Fin (R+1) → UnitAddresses) (fixed : Block (R+1)) (hw : 0<w)
    (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart gen G pub reg args pin x.val u)

local notation "Fields" => PositiveFields reserve ar.n ar.header.d (declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s) (R+1) dim tally
local notation3 (prettyPrint := false) "U" => fun x u => (B x u).start
local notation "mac" => TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n)
local notation "active" => PinStart.preCallSupport U id
local notation3 (prettyPrint := false) "ib" => fun u => (args u).ibase
local notation3 (prettyPrint := false) "hb" => fun u => (args u).hbase
local notation3 (prettyPrint := false) "sb" => fun u => (args u).starbase
local notation "guess" => (fun (_ : {ext // PositiveExterior G args pin w ext}) (_ : Fin (R+1)) => rfl)

local notation "headers" => positiveExteriorFieldsEquiv G args pin L fixed hw size base fit headerWidth
variable {Route : Hist → Type} {Report : (Fin d → Bool) → (q : Hist) → Route q → Type}
  (routed : ∀ (i : Fin d → Bool) (q : Hist) (claim : Fin ((R+1)*dim*tally) → Bool),
    (Σ c : RawBroadcast ar,
      ParsedPreCall G args pin L fixed hw size base fit headerWidth (fun x u => (B x u).start)
        (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) (fun _ _ => rfl) id i ⟨code q,c,claim⟩) ≃
        Σ v : Route q,Report i q v)
variable {gen id G pub reg pin L headerWidth code args fixed hw size base fit B}
local notation3 (prettyPrint := false) "FieldsAt" => PreparedFields (Fin d → Bool) Hist
  (Fin ((R+1)*dim*tally) → Bool) Route Report

open DiagonalTallyCellReports

/-- A cut on this pinned routed inverse belongs to precisely the native prefix reconstructed by
the bare decoder, including its original pin guesses and visited report bank. -/
theorem routedBareTuple_reportCut (f : FieldsAt) (u : Fin (R+1)) {l : ReportLayout}
    {cs : List (ReportCell l)} (rows : ReportAssignments cs)
    (cut : pinnedReportCutAt G args pin L fixed hw size base fit ar headerWidth U ib hb sb guess id
      f.1 (code f.2.1) f.2.2.2.1 ((routed f.1 f.2.1 f.2.2.2.1).symm ⟨f.2.2.1,f.2.2.2.2⟩) u rows) :
    let z := routedBareTuple routed f
    ∃ cur desc, Nonempty (ReportArgumentCut (((B z.1 u).start).visited (z.2 u)).reports rows cur desc) :=
  cut

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
