import OAI.Computability.BorderVNP.DiagonalNativeBootPinStart
import OAI.Computability.BorderVNP.DiagonalNativeValue
import OAI.Computability.BorderVNP.TransmissionPinSlots
import OAI.Computability.BorderVNP.TransmissionPinsComplete

/-! # The retained input of a returned geometry computation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP BurstRAM TeamContraction

/-- Change proven-equal machine inputs without transporting the event list,
final bank or final memory. -/
def Returns.changeInputs {w : ℕ} {c : Code} {p q : Arg → Word w} {a b : TeamOpcode.Macros w 8}
    {s t : Bank w} {m n : Memory w} (ret : Returns c p a s m)
    (publicWords : p=q) (macros : a=b) (registers : s=t) (memory : m=n) :
    Returns c q b t n :=
  ⟨ret.val,by subst q b t n; exact ret.property⟩

/-- The observations used by every later call are the very original ones. -/
theorem Returns.changeInputs_val {w : ℕ} {c : Code} {p q : Arg → Word w} {a b : TeamOpcode.Macros w 8}
    {s t : Bank w} {m n : Memory w} (ret : Returns c p a s m)
    (pub : p=q) (mac : a=b) (bank : s=t) (ram : m=n) :
    (ret.changeInputs pub mac bank ram).val=ret.val := rfl

end RoutingISA.Evaluator

namespace TeamContraction

open VPVNP BurstRAM RoutingISA.Evaluator RoutingISA.Pins

variable {R r t d link inner n w : ℕ} {Edge : Type}
    {G H : Wiring R r t d link inner n Edge} (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool)

/-- A team’s substituted pin width only uses its index and the fixed pin count. -/
theorem Wiring.pinLayout_guessWidth_at (i₀ h₀ s₀ i₁ h₁ s₁ : ℕ) :
    (G.pinLayout u i₀ h₀ s₀).guessWidth=(H.pinLayout u i₁ h₁ s₁).guessWidth := rfl

/-- The literal, exterior and supplied pin bits form the initial memory.
The three later scratch addresses may be chosen independently on both sides. -/
theorem Wiring.processorMemory_at (same : G=H) (i₀ h₀ s₀ i₁ h₁ s₁ : ℕ) :
    let fields := G.processorFields u pin ext i₀ h₀ s₀
    RAMMemory.initialMemory fields.header.length (TeamTapeInputEmit.headerWord w fields.header) =
      processorMemory (H.processorFields u pin ext i₁ h₁ s₁) w := by
  subst H
  rfl

end TeamContraction

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine CellMacro.Generator

/-- The installed evaluator uses the same native routines at the raw startup
and at the pin continuation, independently of the chosen boot witness. -/
theorem BootedPinStart.installed_routines_at {R r t d link inner n w : ℕ} {Edge : Type}
    {gen : Fragment IO} {G : Wiring R r t d link inner n Edge} {pub : Fin (R+1) → Arg → Word w}
    {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses} {pin : Fin d → Bool}
    {ext : Exterior R r link → Bool} {u : Fin (R+1)} (B : BootedPinStart gen G pub reg args pin ext u) :
    install gen n (TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n)) =
      install gen n B.start.routines := rfl

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
