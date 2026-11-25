import OAI.Hierarchy.TaggedWirePathContinuation
import OAI.Hierarchy.TaggedWireCausalTape

namespace OAI
/-! # Positive native packet words suffice to extend a physical history -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape.CounterROM
open ProtocolRAM ProtocolRAM.Calendar ProtocolRAM.PurchaseStage Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {W q d : ℕ} {C : Chart W q d}

/-- A selected row has a nonzero recommended packet. An unselected row has no copies. -/
theorem continuation (R : CounterROM C) (es : List Event) (start : Memory W)
    (positive : ∀ {a : Attempt} {tail : List Event} {x : Memory W},
      Prefix R.format.slot es start (.attempt a :: tail) x → ∀ i : Fin (C.layout a).candidates,
      (C.raw a).batch.packet.eval (HistogramShelf.snapshot C a x) (i.val : Word W) ≠ 0 →
      0 < min (measured (C:=C) a x i) q)
    {tail : List Event} {x : Memory W} (reached : Prefix R.format.slot es start tail x) :
    Nonempty (Path R.format.slot tail x) := by
  apply R.format.continuation es start _ reached
  intro a tail x h i busy
  apply positive h i
  let snap := HistogramShelf.snapshot C a x
  by_cases chosen : (enabledBatch (C.layout a) (repair C a)).selected snap (i.val : Word W)
  · exact chosen.2.1
  · change 0 < (if (enabledBatch (C.layout a) (repair C a)).selected snap (i.val : Word W)
        then (C.raw a).batch.copies else 0) at busy
    rw [ite_eq_right chosen] at busy
    exact False.elim (Nat.not_lt_zero _ busy)

end Hierarchy.WireTelescope.CalendarTape.CounterROM
end

end OAI
