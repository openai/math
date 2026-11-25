import OAI.Computability.BorderVNP.DiagonalCandidateReturnedScan
import OAI.Computability.BorderVNP.DiagonalCandidateFieldReturn

/-! # The returned directory candidate on its installed processor fields -/

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

/-- On an admitted word the selected scan gives a candidate for the actual
installed fields. Its register bank, RAM, charge and chronological evidence
all come from the supplied return. -/
theorem CandidateSite.of_returned_scan_fields
    (source : Diagonal.ReturnedWriterScan ar dir (dir.directory pp lp) pp lp fields f guess pub mac saved ret
      pinRegs pinMem used frame base host key widths old fresh gates outputs field off ell ctl profile claims pad
      word X N cell recv size label decl group owner)
    (origin : (pub 0).val=frame) (space : f.Fits w (pub 0).val) (valid : declarationInRange word)
    (allowed : broadcastAllowed R X ar.header.blocks ar.b ar.K ar.h label recv size word)
    {actualPins : Pins.Layout} (actualFields : Pins.ProcessorFields actualPins)
    (shape : pins=actualPins) (same : HEq fields actualFields)
    (traceFacts : Returns code pub mac regs ram → Prop) (evidence : traceFacts ret) :
    ∃ (r : Returns code pub mac regs ram) (site : CandidateSite (X:=X) ar dir pp lp word owner decl group
        frame base actualPins actualFields f guess pub mac pinRegs pinMem host key widths N cell recv size),
      site.OnReturn old fresh gates outputs field off ell ctl profile claims pad
        r.val.2.1 r.val.2.2 used (traceCost r.val.1) ∧ traceFacts r := by
  obtain ⟨site, observed⟩ := CandidateSite.of_returned_writer_scan source origin space valid allowed
  exact CandidateSite.reindex_fields_return (preRegs:=fun r : Returns code pub mac regs ram => r.val.2.1)
    (preMem:=fun r => r.val.2.2) (charged:=fun r => traceCost r.val.1) (physical:=traceFacts)
    actualFields shape same ⟨ret,site,observed,evidence⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
