import OAI.Computability.BorderVNP.DiagonalSupportedNativeCalls

/-! # The native continuation of a supported, booted team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine CellMacro.Generator BorderVNP.Cube
open PinStart CellDispatch ScheduleClock
open scoped Classical

variable {R r t d link inner n w dim box lanes selectors symbols : ℕ} {Edge : Type}
    (id : TableEntry dim box lanes selectors symbols → ℕ)
    {G : Wiring R r t d link inner n Edge} {pub : Fin (R+1) → Arg → Word w} {reg : Fin (R+1) → Bank w}
    {args : Fin (R+1) → UnitAddresses} {pin : Fin d → Bool}
    (B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G pub reg args pin x.val u)
    (limit : ℕ)

/-- A physical continuation for each team in the actually supported exterior,
at the installed native routines and the original post-boot bank and memory. -/
def NativeNext : Type :=
  (x : {ext // PositiveExterior G args pin w ext ∧ preCallSupport (fun z u => (B z u).start) id ext}) →
  (u : Fin (R+1)) →
  let boot := B ⟨x.val,x.property.1⟩ u
  PositiveContinuation id SparseExterior.driver n (pub u)
    (TeamSiteEvents.macros (w := w) (siteLibrary SparseExterior.driver) (nativeClock n))
    boot.start.bank boot.memory boot.pins boot.used limit

variable (burst : ℕ) (cap : TeamScales.width n (1/2) ≤ burst) (source : NativeSources id B)
    (calls : NativeCalls id B limit burst cap source)

/-- Read the continuation chosen together with its genuine sparse input rows. -/
noncomputable def nativeNext : NativeNext id B limit := calls.next

/-- The rows certified by the sparse team are attached to this literal continuation. -/
theorem nativeNext_eq : nativeNext id B limit burst cap source calls = calls.next := rfl

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
