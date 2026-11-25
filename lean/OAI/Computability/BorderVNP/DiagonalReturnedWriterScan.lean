import OAI.Computability.BorderVNP.DiagonalFrozenRawWriter
import OAI.Computability.BorderVNP.DiagonalFrozenReturnInputs

/-! # The actual geometry return and its signed directory scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Branch Cover Packing Packing.DeckGrid CellEntries
open VPVNP BurstRAM VerifierNetwork RoutingISA RoutingISA.Pins RoutingISA.Transmission
open TeamContraction TeamContraction.ProcessorSlots GeometryAdvice GeometryFrameEncoding PackedHistoryCircuit
open Packing.RoutingOutputs CubeHeaderInstall
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.Tally Cube.LabelIndex Cube.MeanChoice CellAddresses
open Directory.PrivateBank CellAddressPhysical CellAddressCircuit RoutingISA.Evaluator LocalRow TeamContraction.JointHeader CompactMachine

/-- The selected geometry return, its placement epoch and its route-guarded
directory scan, with the original emitted rows and both native time bounds. -/
def ReturnedWriterScan {w R dim : ℕ} {Port I : Type*} [Fintype I] {bits : Port → ℕ}
    (ar : CubeArena.Layout) (dir : Directory.Layout) (rows : List Directory.Row)
    (pp lp : ℕ → ℕ × ℕ) {pins : Pins.Layout} (fields : Pins.ProcessorFields pins) (f : BroadcastFrame)
    (guess : ℕ → Bool) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    {code : Code} {regs : Bank w} {ram : Memory w} (saved ret : Returns code pub mac regs ram)
    (pinRegs : Bank w) (pinMem : Memory w) (used frame base : ℕ)
    (host : I → Fin ar.cells) (key : I ↪ ℕ) (widths : I → ℕ)
    (old : Fin 81 → Word w) (fresh gates outputs field off ell ctl : ℕ)
    (profile : List Bool) (claims : List (List Bool)) (pad : ℕ) (word : Broadcast ar.n ar.header.d ar.header.cap)
    (exterior : ℕ) (N : Network dim Port bits) (cell : N.Site → Fin ar.cells)
    (recv : Fin rows.length → Fin ar.cells) (size : Fin rows.length → ℕ)
    (label : Fin ar.cells → Label (ar.n+1) ar.header.d) (decl : LengthDeclaration ar.n ar.header.d)
    (group : Fin ar.header.d → Fin (R+1)) (owner : ℕ → Fin (R+1)) : Prop :=
  saved=ret ∧
  ∃ (epoch : Returns epochPlacement pub mac pinRegs pinMem)
    (published : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2) (mid : Memory w)
    (scan : Returns (.seq PrivatePlacement.program Directory.ISA.program) pub mac saved.val.2.1 saved.val.2.2),
    let L := LabelIndex.layout frame (readings scan.val.2.2)
    epoch.val.2.2=mid ∧ published.val.2.2=Directory.ISA.publish mid (pub 0).val base rows ∧
    epoch.val.1.flatMap TeamRAM.Event.choices=[] ∧
    used+traceCost epoch.val.1+traceCost published.val.1≤traceCost ret.val.1+deliveryScanTicks dir.entries dir.teams dir.sites ∧
    scan.val.2=published.val.2 ∧ traceCost scan.val.1≤deliveryScanTicks dir.entries dir.teams dir.sites ∧
    ProfileRouteInputs fields f pub guess published.val.2.2 ∧
    fields.header.length=(pub 0).val ∧ (∀ count,TablePointers (ar.table frame count) (readings published.val.2.2)) ∧
    Nonempty (SlottedWriter ar dir pp lp pins pub mid base host key widths) ∧
    SignedPrep.PinnedRawInput (ar:=ar) (D:=dir) (pp:=pp) (lp:=lp) (pub:=pub) (slotted:=mid) (base:=base)
      f old fresh gates outputs field off ell ctl profile claims pad word R exterior ∧
    PublishedRowPlacement N cell recv size (pub 0).val scan.val.2.2 ∧
    (declarationInRange word → broadcastAllowed R exterior ar.header.blocks ar.b ar.K ar.h label recv size word →
      Nonempty (SignedPrep.HeaderWriterReceipt ar dir pp lp owner decl group pins f pub mac scan.val.2.1 scan.val.2.2)) ∧
    L.cells=ar.cells ∧ L.cableCount=ar.cables ∧ L.deliveryCount=rows.length ∧ L.labels=ar.alphabet

end Diagonal

end BorderVNP
end Computability
end OAI
