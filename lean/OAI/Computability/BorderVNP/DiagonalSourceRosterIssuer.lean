import OAI.Computability.BorderVNP.DiagonalSizedIssuedDecoder

/-! # The original report roster for an issued decoder -/

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

/-- The original core, its free-input chart and the immutable cell and owner
assignment used by every continuation of this reader. -/
structure SourceRoster (d symbols : ℕ) where
  /-- The free-port values decoded from the original reader pins. -/
  ports : (Fin d → Bool) → Ports bits
  /-- The published owner number of each source site row. -/
  site : ∀ h, Fin (core h).siteRows → ℕ
  /-- The ordered original bottom bundles at each global core cell. -/
  bundles : ∀ h, Fin (core h).cells → List Bundle
  /-- The report layout for each team on the attained route. -/
  charts : (Fin d → Bool) → (h : Hist) → (core h).Route symbols → Fin (R+1) → ReportLayout
  /-- The ordered reported cells and their original global ordinal map. -/
  rows : ∀ i h v, ReceivedRows (charts i h v) (core h).cells
  /-- The team assigned to each global cell by the attained routing declaration. -/
  team : ∀ h, (core h).Route symbols → Fin (core h).cells → Fin (R+1)
  /-- A received ordinal is assigned to the team whose list contains it. -/
  order : ∀ i h v u j, team h v ((rows i h v).order ⟨u,j⟩)=u

variable {id G pub reg pin L headerWidth code args fixed hw size base fit B}
    (roster : SourceRoster core d symbols) (taskBase : ℕ)

/-- Apply a measured native decoder to a single coherent source roster. -/
noncomputable def PreparedHistoryDecoder.issuerFromRoster :=
  PreparedHistoryDecoder.issuerAtSize decoder limit burst privateSize core roster.ports roster.site roster.bundles
    roster.charts roster.rows roster.team roster.order taskBase

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
