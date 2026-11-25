import OAI.Computability.BorderVNP.DiagonalNativeBootPinStart
import OAI.Computability.BorderVNP.DiagonalNativeProfilePrefix
import OAI.Computability.BorderVNP.DiagonalPositiveExteriorRoutes
import OAI.Computability.BorderVNP.DiagonalPositiveHeaderClaims

/-! # Geometry returns forced by a jointly prepared exterior -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator Routing ProcessorSlots JointHeader
open CellMacro.Generator BorderVNP.Cube

variable {R r link : ℕ} {L : WireLayout (R+1) r link} {hdr : List Bool}

/-- All copied broadcast bits equal the parsed header on this exterior, for
arbitrary relay and payload wires. -/
theorem HeaderExterior.broadcast_eq (ext : HeaderExterior L hdr) (len : hdr.length = L.header) (b : Block (R+1)) :
    (L.exteriorEquiv ext.val).broadcast b = headerBits hdr len := by
  funext j
  have whole := ext.property b
  change List.ofFn ((L.exteriorEquiv ext.val).broadcast b) = hdr at whole
  have entry := List.getElem_of_eq (i := j.val) whole (by simp)
  simpa only [List.getElem_ofFn, headerBits] using entry

namespace ProcessorSlots
open RoutingISA.CompactMachine PackedHistoryCircuit

variable {t d inner n w axes box lanes selectors symbols : ℕ} {Edge : Type}
    {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}
    {G : Wiring R r t d link inner n Edge} {pub : Fin (R+1) → Arg → Word w}
    {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses} {pin : Fin d → Bool}
    {ext : Exterior R r link → Bool} {u : Fin (R+1)}
    (B : BootedPinStart gen G pub reg args pin ext u)

/-- The genuine pin and preparation at this booted team contain a returning
execution of the installed guarded geometry, starting at its actual time-zero RAM. -/
theorem BootedPinStart.profileOfPrefix (p : B.start.Prefix id) :
    let ad := args u
    let fields := G.processorFields u pin ext ad.ibase ad.hbase ad.starbase
    let native := TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)
    Nonempty (Returns (withStartup pinGeometry) (pub u) native (reg u) (processorMemory fields w)) := by
  intro ad fields native
  have run : Runs (pub u) (install gen n native) bootHeader (reg u) (processorMemory fields w)
      B.trace B.out B.memory := by
    rw [←siteLibrary_installed gen n]
    exact B.boot
  have geometry := profile_from_preparation (G.transferFrame u ad.header ad.dst) run B.stable B.positive
    B.pins p.1 p.2
  rw [←siteLibrary_installed gen n] at geometry
  exact geometry

end ProcessorSlots
end TeamContraction

end BorderVNP
end Computability
end OAI
