import OAI.Computability.BorderVNP.DiagonalIssuedHeaderAssertions
import OAI.Computability.BorderVNP.DiagonalIssuedChargeDomains

/-! # The measured post-call assertion on the issued roster -/

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

open RoutingISA.Evaluator.ScheduleClock RoutingISA.SignedTaskArena

variable (task : SignedTaskArena.Layout) (A : StartupArena) (cost : PhaseCharges)
    (entryWords indexBits tallyDim subt P L₀ F H : ℕ)

attribute [local irreducible] PinStart.ChargedPost routedBareTuple

set_option cleanup.letToHave false in
set_option maxRecDepth 6500 in
set_option maxHeartbeats 1200000 in
/-- The complete native post-call charges at the original tuples of this roster. -/
def PreparedHistoryDecoder.allPostsAtRoster : Prop :=
  AllIssuedPost (id:=id) (B:=B) (routed:=routed) (task:=task) (A:=A) (cost:=cost)
    (entryWords:=entryWords) (indexBits:=indexBits) (tallyDim:=tallyDim) (subt:=subt)
    (P:=P) (L₀:=L₀) (F:=F) (H:=H)

set_option cleanup.letToHave false in
set_option maxRecDepth 6500 in
set_option maxHeartbeats 1200000 in
/-- Collect the scalar charge established at each observed header in the normal
native clock's family, at the same original joint preparation and team. -/
theorem PreparedHistoryDecoder.allPostsOfHeaderAssertions :
    decoder.HeaderAssertions limit burst privateSize core roster taskBase routed
      (fun x active u _ _ => PinStart.ChargedPost id (fun v => (B x v).start) cost.argumentsCalls task A
        entryWords indexBits tallyDim subt P L₀ F H active u) →
      decoder.allPostsAtRoster limit burst privateSize core roster taskBase routed task A cost
        entryWords indexBits tallyDim subt P L₀ F H := by
  intro measured
  exact fun f u => measured f u

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
