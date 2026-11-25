import OAI.Computability.BorderVNP.DiagonalIssuedObservedFields
import OAI.Computability.BorderVNP.DiagonalIssuerRouteDomain

/-! # Consequences of assertions on the actual issued headers -/

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

variable (P T : (x : {ext // PositiveExterior G args pin w ext}) →
    PinStart.JointPrefix id (fun i => (B x i).start) → Fin (R+1) →
    (fields : PositiveFields reserve axes groups cap (R+1) dim tally) →
    fields.bits = observed L x.val fixed → Prop)

set_option maxRecDepth 6500 in
set_option maxHeartbeats 1200000 in
/-- A test evaluated on the exact exterior, joint prefix and observed header of every
team at every issued roster field. -/
def PreparedHistoryDecoder.HeaderAssertions : Prop :=
  ∀ (f : _) (u : Fin (R+1)),
    let z := routedBareTuple routed f
    P z.1 z.2 u (issuedHeader routed f) (routedBareTuple.observed routed f fixed).symm

set_option maxRecDepth 6500 in
set_option maxHeartbeats 1200000 in
/-- Apply an implication at the same recovered header and native preparation on which
its premise was established. -/
theorem PreparedHistoryDecoder.headerAssertionsMap
    (each : ∀ x active u fields seen, P x active u fields seen → T x active u fields seen) :
    decoder.HeaderAssertions limit burst privateSize core roster taskBase routed P →
      decoder.HeaderAssertions limit burst privateSize core roster taskBase routed T := by
  intro actual f u
  let z := routedBareTuple routed f
  exact each z.1 z.2 u (issuedHeader routed f) (routedBareTuple.observed routed f fixed).symm (actual f u)

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
