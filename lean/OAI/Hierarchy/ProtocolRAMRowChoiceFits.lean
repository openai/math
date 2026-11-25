import OAI.Hierarchy.ProtocolRAMRowChoice

namespace OAI
/-! # Input-bank bounds for a finite native field selector -/

namespace Hierarchy.ProtocolRAM.BoughtSockets
variable {w : ℕ}

theorem choose_fits_bound {out : ℕ} (n start : ℕ) (xs : Fin n→Expr) (which : Expr)
    (terms : ∀i,(xs i).Fits w out) (index : which.Fits w out) : (chooseField n start xs which).Fits w out := by
  induction n generalizing start with
  | zero => trivial
  | succ n ih => exact ⟨index,trivial,terms 0,ih _ _ (fun i=>terms i.succ)⟩

end Hierarchy.ProtocolRAM.BoughtSockets

end OAI
