import OAI.Computability.BorderVNP.RoutingISAEvaluator
import OAI.Computability.BorderVNP.RoutingISAExtendedFrame
import OAI.Computability.BorderVNP.GeometryAdvicePipeline
import OAI.Computability.BorderVNP.TransmissionDataWriter
import OAI.Computability.BorderVNP.DiagonalTallyPacketLookup
import OAI.Computability.BorderVNP.DiagonalTallyMaterialize

/-! # Physically staged instructions of the signed matrix evaluator

The literal and epoch-program loaders, raw data lowering, per-packet finite
table lookup, and tally materialization are part of the static word table.
The remaining group instructions specify the label and ownership computations
and the local scatter and cell argument preparation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM

/-- Prepare owners, emit original literal and pin delivery rows, and append the
shared selector and crossing lists computed from the declared group widths. -/
def publicGroups (owners shared : Code) : Code :=
  .block [owners, Transmission.DataWriter.program, shared]

/-- Only the true per-packet table lookup and checked per-cell reported data
supply the occurrence counts passed to the native tally stage. -/
def tallied (requests : Code) : Code :=
  .block [requests, DiagonalTallyPacket.packetLookup, DiagonalTallyMaterialize.materialize]

/-- Native staged evaluator, with its ordinary literal frame installation,
Boolean epoch-frame evaluation, concrete transmission-row writer and residue
query evaluator all included in the assembled instruction table. -/
def staged (owners shared arguments requests : Code) : Code :=
  assemble ExtendedFrame.install GeometryAdvice.reconstruct (publicGroups owners shared)
    arguments (tallied requests)

/-- A native path through the staged table runs through the physical loads,
validations and private calls in exactly the order encoded by the assembler. -/
theorem staged_execute_iff {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {owners shared arguments requests : Code}
    (ho : owners.withoutAccept = true) (hs : shared.withoutAccept = true)
    (ha : arguments.withoutAccept = true) (hr : requests.withoutAccept = true)
    {s : Bank w} {m bits es} :
    let c := staged owners shared arguments requests
    TeamRAM.execute (c.program.fetch pub macros) ⟨0,s⟩ m bits = some es ↔
      (∃ t mt, Runs pub macros c s m es t mt) ∧ es.map TeamRAM.Event.choices = bits := by
  have data : Transmission.DataWriter.program.withoutAccept = true := by decide
  have packet : DiagonalTallyPacket.packetLookup.withoutAccept = true := by decide
  have reports : DiagonalTallyMaterialize.materialize.withoutAccept = true := by decide
  exact execute_iff (by decide) (by decide)
    (by simp only [publicGroups,Code.block,Code.withoutAccept,ho,data,hs,Bool.and_self]) ha
    (by simp only [tallied,Code.block,Code.withoutAccept,hr,packet,reports,Bool.and_self])

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
