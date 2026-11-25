import OAI.Computability.BorderVNP.DiagonalIssuerRouteDomain
import OAI.Computability.BorderVNP.DiagonalSuppliedOriginalDirectories

/-! # Data-valued original input on the physical issuer's route -/

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

variable {Keys Slots : Hist → Type} {cells : Hist → ℕ}
    (directory : (h : Hist) → CellPacketGeometry.SiteWords.Directory (Keys h) (Slots h) (cells h+1))

/-- The packet map at the already attained routing on this physical roster. -/
noncomputable def PreparedHistoryDecoder.SuppliedPacketsAtRoute : Type _ :=
  type_of% (decoder.originalPacketMap core roster.ports roster.site roster.bundles roster.charts roster.rows
    roster.team taskBase directory routed)

/-- Retain each supplied native launch along the very routing used by the
physical issuer, with its owner and original signed row data. -/
noncomputable def PreparedHistoryDecoder.suppliedPacketsAtRoute :
    decoder.SuppliedPacketsAtRoute limit burst privateSize core roster taskBase routed directory :=
  decoder.originalPacketMap core roster.ports roster.site roster.bundles roster.charts roster.rows
    roster.team taskBase directory routed

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
