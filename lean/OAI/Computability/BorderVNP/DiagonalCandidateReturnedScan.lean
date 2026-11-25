import OAI.Computability.BorderVNP.DiagonalReturnedWriterScan
import OAI.Computability.BorderVNP.DiagonalSignedCandidateSiteSelection

/-! # The typed candidate on the actual returned directory scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP BurstRAM Crossing Packing RoutingISA RoutingISA.Transmission TeamContraction
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.Tally LabelIndex PackedHistoryCircuit LocalRow

variable {w R dim X : ℕ} {Port I : Type*} [Fintype I] {bits : Port → ℕ}
    {ar : CubeArena.Layout} {dir : Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {pins : Pins.Layout} {fields : Pins.ProcessorFields pins} {f : BroadcastFrame}
    {guess : ℕ → Bool} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {code : Code} {regs : Bank w} {ram : Memory w} {saved ret : Returns code pub mac regs ram}
    {pinRegs : Bank w} {pinMem : Memory w} {used frame base : ℕ}
    {host : I → Fin ar.cells} {key : I ↪ ℕ} {widths : I → ℕ} {old : Fin 81 → Word w}
    {fresh gates outputs field off ell ctl : ℕ} {profile : List Bool} {claims : List (List Bool)} {pad : ℕ}
    {word : Broadcast ar.n ar.header.d ar.header.cap} {N : Network dim Port bits}
    {cell : N.Site → Fin ar.cells} {recv : Fin (dir.directory pp lp).length → Fin ar.cells}
    {size : Fin (dir.directory pp lp).length → ℕ} {label : Fin ar.cells → Label (ar.n+1) ar.header.d}
    {decl : LengthDeclaration ar.n ar.header.d} {group : Fin ar.header.d → Fin (R+1)} {owner : ℕ → Fin (R+1)}

/-- On an admitted broadcast the saved directory scan yields a native candidate
whose registers, RAM, and charge are those of the supplied geometry return. -/
theorem CandidateSite.of_returned_writer_scan
    (source : Diagonal.ReturnedWriterScan ar dir (dir.directory pp lp) pp lp fields f guess pub mac saved ret
      pinRegs pinMem used frame base host key widths old fresh gates outputs field off ell ctl profile claims pad
      word X N cell recv size label decl group owner)
    (origin : (pub 0).val=frame) (space : f.Fits w (pub 0).val) (valid : declarationInRange word)
    (allowed : broadcastAllowed R X ar.header.blocks ar.b ar.K ar.h label recv size word) :
    ∃ site : CandidateSite (X:=X) ar dir pp lp word owner decl group frame base pins fields f guess pub mac pinRegs pinMem
        host key widths N cell recv size,
      site.OnReturn old fresh gates outputs field off ell ctl profile claims pad ret.val.2.1 ret.val.2.2 used (traceCost ret.val.1) := by
  obtain ⟨rfl,checked⟩ := source
  exact CandidateSite.of_checked_scan old fresh gates outputs field off ell ctl profile claims pad _ _ used _
    origin space valid allowed checked

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
