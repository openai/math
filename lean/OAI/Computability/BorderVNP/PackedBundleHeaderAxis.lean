import OAI.Computability.BorderVNP.PackedBundleBankConfig
import OAI.Computability.BorderVNP.CubeRouteDataLayouts

/-! # Independence of the published bundle addresses from the declared axis -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.BundleSort

open RoutingISA VPVNP.VerifierNetwork

/-- Equality of the physical receiving addresses is sufficient even if the
two bank records differ in scratch area, team frame or declared axis. -/
theorem bankConfig_eq_of_addresses {σ : Type} [Fintype σ] {w : ℕ}
    (a b : CellBanks.Layout) (cells gap : ℕ) (valid : Frame σ Unit)
    (same : ∀ c : Fin cells, a.bank c.val=b.bank c.val) :
    bankConfig (w:=w) {a with cells := cells} gap valid =
      bankConfig {b with cells := cells} gap valid := by
  unfold bankConfig
  congr 1
  funext i
  rcases i with ⟨c,k⟩ | i
  · change PackedHistogram.fixed (Fin.ofNat (2^w) (a.bank c.val+gap)) k =
      PackedHistogram.fixed (Fin.ofNat (2^w) (b.bank c.val+gap)) k
    rw [same c]
  · rfl

/-- The header table stores a fixed receiving address for each cell. The
declared axis only enters the later loop that computes owners. -/
theorem bankConfig_cellWriter_axis {σ : Type} [Fintype σ] {w : ℕ}
    (a : CubeArena.Layout) (frame control cells gap : ℕ) (u v : Fin (a.n+1)) (valid : Frame σ Unit) :
    bankConfig (w:=w) {a.cellWriter frame control u with cells := cells} gap valid =
      bankConfig {a.cellWriter frame control v with cells := cells} gap valid := by
  exact bankConfig_eq_of_addresses _ _ cells gap valid (fun _ => rfl)

end Packing.BottomReports.BundleSort

end BorderVNP
end Computability
end OAI
