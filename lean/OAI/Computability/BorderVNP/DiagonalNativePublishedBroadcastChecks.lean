import OAI.Computability.BorderVNP.DiagonalPublishedBroadcastChecks
import OAI.Computability.BorderVNP.DiagonalBootedPinLibrary

/-! # Broadcast validation on the installed native program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP BurstRAM RoutingISA RoutingISA.CompactMachine RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open RoutingISA.LocalRow PackedHistoryCircuit Packing Crossing _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.LabelIndex

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {pub : Fin (R+1) → Arg → Word w}
    {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses} {ar : CubeArena.Layout}
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    {u : Fin (R+1)} (B : BootedPinStart SparseExterior.driver G pub reg args pin ext u)
local notation3 (prettyPrint := false) "lib" => install SparseExterior.driver n
  (TeamSiteEvents.macros (w:=w) (siteLibrary SparseExterior.driver) (nativeClock n))
local notation3 (prettyPrint := false) "frame₀" => G.transferFrame u (args u).header (args u).dst
local notation3 (prettyPrint := false) "fields₀" => G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase
local notation3 (prettyPrint := false) "Full" => Returns (withStartup pinGeometry) (pub u) lib (reg u)
  (processorMemory fields₀ w)
variable {dir : Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {pins : Pins.Layout} {mid : Memory w} {base : ℕ}
    {I : Type*} [Fintype I] {host : I → Fin ar.cells} {key : I ↪ ℕ} {width : I → ℕ}
    (writer : SlottedWriter ar dir pp lp pins (pub u) mid base host key width)
    (old : Fin 81 → Word w) (fresh gates outputs bitWidth off ell controls : ℕ)
    (word : List Bool) (claims : List (List Bool)) (pad : ℕ) (raw : Broadcast ar.n ar.header.d ar.header.cap) (X : ℕ)
    (input : PinnedRawInput (ar:=ar) (D:=dir) (pp:=pp) (lp:=lp) (pub:=pub u) (slotted:=mid) (base:=base)
      (G.transferFrame u (args u).header (args u).dst) old fresh gates outputs bitWidth off ell controls word claims pad raw R X)

local notation3 (prettyPrint := false) "dd" => dir.directory pp lp
local notation3 (prettyPrint := false) "pubMem" => Directory.ISA.publish mid (pub u 0).val base dd
local notation3 (prettyPrint := false) "sizes" => fun i : Fin (dd).length => (dd)[i.val].width

include writer input in
set_option maxRecDepth 5500 in
/-- The early checker uses the native installed library at the original
startup, for arbitrary substituted bits on this team. -/
theorem published_native_broadcast_checks (g : Fin B.start.guessWidth → Bool) :
    ∀ (profile : (Fin B.start.guessWidth → Bool) ≃ Full)
    (_spelling : ∀ v, (profile v).val.1.flatMap TeamRAM.Event.choices=List.ofFn v)
    (scan : Returns (.seq PrivatePlacement.program Directory.ISA.program) (pub u) lib (profile g).val.2.1 (profile g).val.2.2)
    (_stored : scan.val.2.2=pubMem)
    {dim : ℕ} {Names : Type*} {bits : Names → ℕ} (N : Network dim Names bits)
    (tile : N.Site → Fin ar.cells) (recv : Fin (dd).length → Fin ar.cells)
    (_placed : PublishedRowPlacement N tile recv sizes (pub u 0).val scan.val.2.2) (hd : 0<ar.header.d),
    let label := meanPackedLabel N tile recv sizes (List.finRange ar.cells) ar.n ar.header.d hd
    ∀ code : B.start.Prefix id, code.1=g →
      declarationInRange raw ∧ broadcastAllowed R X ar.header.blocks ar.b ar.K ar.h label recv sizes raw := by
  rw [← B.installed_routines]
  exact published_broadcast_checks id B writer old fresh gates outputs bitWidth off ell controls word claims pad raw X input g

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
