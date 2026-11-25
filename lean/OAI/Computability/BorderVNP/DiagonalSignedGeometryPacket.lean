import OAI.Computability.BorderVNP.CubeRouteJointPacket
import OAI.Computability.BorderVNP.RoutingISASignedStartupExtension

/-! # One extension for the signed geometry, routing directory and cube cells -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA CubeHeaderInstall Packing RoutingOutputs GeometryAdvice

variable {w : ℕ}

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2200000 in
/-- Installing the directory in the supplied old words before building a signed
task gives the same 81-word array as the physical directory and cube overlays.
Every surviving old word is preserved at its original address. -/
theorem signed_routing_extension (task : SignedTaskArena.Layout) (old : Fin 81 → Word w) (D : Directory.Layout)
    (origin edges cells raw team subtotalWidth : ℕ) :
    task.extension raw team subtotalWidth (routingExtension old D origin edges cells) =
      task.cube.extension (routingExtension (task.extension raw team subtotalWidth old) D origin edges cells) := by
  have repack (v : Word w) : TeamTapeInputEmit.word w v.val = v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
  funext i
  fin_cases i <;> first | rfl | exact repack _

/-- The geometry packet's pinned input vector, including the routing words,
is exactly the signed extension read by native demand publication. -/
theorem signed_geometry_packet (task : SignedTaskArena.Layout) (old : Fin 81 → Word w) (D : Directory.Layout)
    (origin edges cells raw team subtotal fresh profile gates outputs width off ell : ℕ) :
    Allocation.fields
      (pinFields (task.extension raw team subtotal (routingExtension old D origin edges cells))
        (Allocation.stop fresh profile gates outputs width w) task.cube.header.d (task.cube.n+1)
        (task.cube.h*task.cube.b) task.cube.header.blocks profile
        (Cube.Physical.declarationCap task.cube.n task.cube.header.d task.cube.header.blocks task.cube.b task.cube.h task.cube.s))
      fresh profile gates outputs width off ell =
      signedProfileExtension task old D origin edges cells raw team subtotal fresh profile gates outputs width off ell := by
  rw [signed_routing_extension]
  rfl

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
