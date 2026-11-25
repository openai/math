import OAI.Hierarchy.ProbeFixedTerminalCash
import OAI.Hierarchy.ProbeFixedPhase
import OAI.Hierarchy.ProtocolRAMCalendarStockActual
import OAI.Hierarchy.ProtocolRAMCalendarStockTrials

namespace OAI
/-! # Uniform inventory ceiling at all public outer and reserve dates -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage StockBound
variable {F : Type*} [Field F] {k z arity goods w : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)

theorem stock_cap (C : Chart w arity goods) (mesh : C.mesh=v.mesh) (arena : Arena)
    (f : Attempt→Format z (2^v.W) k arity goods) (initial empty width : ℕ) (bills : Event→WordRows) (start : Memory w)
    (r : Run C (pricedBanks v.mesh arena f initial empty) start z (CoreBoard.Stages z (2^v.W)) k (v.keepLimit*width)) :
    let A := v.account arena f initial width bills
    (∀p< C.mesh.inject+C.mesh.cool,∀h≤ C.mesh.outerFuel,∀i,(A.trial C start p h).bits i≤ v.keepLimit*width) ∧
    ∀p< C.mesh.inject+C.mesh.cool,∀h< C.mesh.outerFuel,∀j< C.mesh.reserveSteps,∀t≤ C.mesh.innerFuel,∀i,
      (A.inner C start p h j t).bits i≤ v.keepLimit*width := by
  intro A
  let bank := pricedBanks v.mesh arena f initial empty
  have addr (a : Attempt) (e : Event) (pos : position v.mesh (.attempt a)=position v.mesh e)
      (i : Commodity (Fin (2^z)) (CoreBoard.Stages z (2^v.W)) k) :
      A.stockAt a i=bank.previous C.mesh e+PurchaseInventory.slot i := by
    change previousStock v.mesh initial (publishedStock v.mesh arena f) (.attempt a)+_=
      previousStock C.mesh initial (publishedStock v.mesh arena f) e+_
    rw [mesh]
    simp only [previousStock,pos]
  constructor
  · intro p hp h hh i
    rcases lt_or_eq_of_le hh with live|rfl
    · exact r.trial A p h hp live (addr _ _ rfl) i
    · exact r.trial_end A p hp (addr _ _ (by rw [mesh]; rfl)) i
  · intro p hp h hh j hj t ht i
    rcases lt_or_eq_of_le ht with live|rfl
    · exact r.inner A p h j t hp hh hj live (addr _ _ rfl) i
    · exact r.inner_end A p h j hp hh hj (addr _ _ (by rw [mesh]; rfl)) i

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
