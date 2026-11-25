import OAI.Computability.BorderVNP.DiagonalCalendarPublishedBanks

/-! # Apply a retained publication at one native prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.SignedTaskArena Routing JointHeader

/-- Read the protected source banks on the actual prefix with the observed header. -/
theorem PublishedReadbackFamily.readAt {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pub : Fin (R+1) → Arg → Word w} {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
    {pin : Fin d → Bool} (task : SignedTaskArena.Layout)
    (boot : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G pub reg args pin x.val u)
    {A : StartupArena} {L : WireLayout (R+1) r link} {fixed : Block (R+1)} {dest entries indices : ℕ}
    (read : PublishedReadbackFamily task boot A L fixed dest entries indices)
    (x : {ext // PositiveExterior G args pin w ext})
    (active : PinStart.JointPrefix task.id (fun u => (boot x u).start)) (u : Fin (R+1))
    (p : PositiveFields task.cube.header.profile task.cube.n task.cube.header.d task.cube.header.cap
      task.cube.teams task.dim w) (same : p.bits=observed L x.val fixed) :
    BootedPinStart.PublishedSourceReadback task (boot x) active u A p dest entries indices := by
  intro wire₀ hdr₀ len₀ pub₀ op₀ regs₀ mem₀ who sourceFrame site proto amount route owned
  exact read x active u p same sourceFrame site owned

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
