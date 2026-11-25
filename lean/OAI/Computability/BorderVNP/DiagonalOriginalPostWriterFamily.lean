import OAI.Computability.BorderVNP.DiagonalWriterPostRequest
import OAI.Computability.BorderVNP.DiagonalSourceReadbackAt

/-! # Physical post requests on the original positive starts -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.SignedTaskArena Routing JointHeader

/-- Build a post request at every actual positive exterior and native prefix
for the header observed on its physical wires. -/
def OriginalWriterFamily {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pub : Fin (R+1) → Arg → Word w} {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
    {pin : Fin d → Bool} (task : SignedTaskArena.Layout)
    (boot : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G pub reg args pin x.val u)
    (L : WireLayout (R+1) r link) (fixed : Block (R+1)) : Type :=
  (x : {ext // PositiveExterior G args pin w ext}) →
    (active : PinStart.JointPrefix task.id (fun i => (boot x i).start)) → (u : Fin (R+1)) →
    (p : PositiveFields task.cube.header.profile task.cube.n task.cube.header.d task.cube.header.cap task.cube.teams task.dim w) →
    p.bits=observed L x.val fixed → FragmentRows.WriterPostRequest task (boot x) active u

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
