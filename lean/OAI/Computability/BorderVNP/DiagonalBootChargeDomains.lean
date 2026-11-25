import OAI.Computability.BorderVNP.DiagonalIssuedJointCharge

/-! # Clocks and charged visits of one physical boot family -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine BorderVNP.Cube

variable {R r time width link inner n w : ℕ} {Edge : Type}
    {G : Wiring R r time width link inner n Edge}
    {pub : Fin (R+1) → Arg → Word w} {reg : Fin (R+1) → Bank w}
    {args : Fin (R+1) → UnitAddresses} {pin : Fin width → Bool}
    (B : (x : {e // PositiveExterior G args pin w e}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G pub reg args pin x.val u)
    {cn cb ch cK cs : ℕ} (id : TableEntry cn cb ch cK cs → ℕ)
    (cost : ScheduleClock.PhaseCharges)

/-- Every exterior with an attained tuple of positive prefixes obeys the
phase clock on this same family of booted original processors. -/
def SupportedBootClock : Prop :=
  ∀ x : {e // PositiveExterior G args pin w e ∧
      PinStart.preCallSupport (fun y u => (B y u).start) id e},
    let nodes := B ⟨x.val,x.property.1⟩
    PinStart.JointClock id (fun u => (nodes u).start) (fun u => (nodes u).used) cost

/-- The reader, argument and returning-call receipts at every team of each
actually attained prefix tuple. -/
def AllBootChargedVisits (task : SignedTaskArena.Layout) (A : StartupArena)
    (entryWords indexBits dim tallyWidth publicTicks localTicks finishTicks readerTicks : ℕ) : Prop :=
  ∀ (x : {e // PositiveExterior G args pin w e})
      (a : PinStart.JointPrefix id (fun v => (B x v).start)) (u : Fin (R+1)),
    PinStart.ChargedVisit id (fun v => (B x v).start) (fun v => (B x v).used)
      cost task A entryWords indexBits dim tallyWidth publicTicks localTicks finishTicks readerTicks a u

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
