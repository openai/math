import OAI.Computability.BorderVNP.DiagonalIssuedObservedFields
import OAI.Computability.BorderVNP.DiagonalIssuerRouteDomain

/-! # Dependent native data on the original issued header -/

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
    (decoder : PreparedHistoryDecoder SparseExterior.driver id G pub reg pin L headerWidth code args fixed hw size base fit B)
    (limit burst : ℕ) (privateSize : TeamScales.width n (1/2) ≤ burst)

open Crossing Packing.Inherited Packing.BottomReports Cube.Physical Cube.Physical.NativeAssignments
open DiagonalTallyCellReports RoutingISA.CompactMachine
variable {D nativeGroups : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Hist → Network D P bits} {count : Hist → ℕ}
    (core : ∀ h, CoreDirectory (N h) axes nativeGroups (count h) box lanes selectors R)

variable {id G pub reg pin L headerWidth code args fixed hw size base fit B}
    (roster : SourceRoster core d symbols) (taskBase : ℕ)

variable (routed : decoder.RosterRoutes limit burst privateSize core roster taskBase)

variable (data : (x : {ext // PositiveExterior G args pin w ext}) →
    PinStart.JointPrefix id (fun i => (B x i).start) → Fin (R+1) →
    (fields : PositiveFields reserve axes groups cap (R+1) dim tally) →
    fields.bits = observed L x.val fixed → Type)

set_option maxRecDepth 6500 in
set_option maxHeartbeats 1200000 in
/-- Each issued team carries native data indexed by its recovered header and
the observation of those bits on the original positive exterior. -/
noncomputable def PreparedHistoryDecoder.OriginalRouteHeaderData : Type :=
  (f : _) → (u : Fin (R+1)) →
    let z := routedBareTuple routed f
    let fields := issuedHeader routed f
    data z.1 z.2 u fields (routedBareTuple.observed routed f fixed).symm

set_option maxRecDepth 6500 in
set_option maxHeartbeats 1200000 in
/-- Apply the physical source to the actual header and observation supplied
by this roster's inverse, before any report or subtotal is tested. -/
noncomputable def PreparedHistoryDecoder.collectOnRouteHeaders
    (source : ∀ x active u (fields : PositiveFields reserve axes groups cap (R+1) dim tally)
      (seen : fields.bits = observed L x.val fixed), data x active u fields seen) :
    decoder.OriginalRouteHeaderData limit burst privateSize core roster taskBase routed data :=
  fun f u =>
    let z := routedBareTuple routed f
    source z.1 z.2 u (issuedHeader routed f) (routedBareTuple.observed routed f fixed).symm

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
