import OAI.Hierarchy.ProbeStockQuotes
import OAI.Hierarchy.ProtocolRAMPurchaseDensity
import OAI.Hierarchy.ProbePayloadStrip

namespace OAI
/-! # The same motion energy on the typed commodity plane and on the actual CT scan -/

namespace Hierarchy.ProtocolRAM.PurchaseCT
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open scoped BigOperators Classical
noncomputable section

/-- CT records are traversed stage-major. Prices address them by payload, then by
stage number. This permutation is independent of the current selector and stock. -/
def tileAddress (z d : ℕ) : Tile z d ≃ Fin (2^z) × Fin (2*rounds d+1) where
  toFun v := (v.2,stageNumber v.1)
  invFun p := ⟨p.2.cast (template_length (radix z d) (radix_pos z d) (rounds d) Unit (2^z)).symm,p.1⟩
  left_inv := by rintro ⟨s,p⟩; rfl
  right_inv := by rintro ⟨p,s⟩; rfl

theorem measured_motion {z d k : ℕ} (phase : PhasePrice) (payload signed base : ℕ)
    (raw : Memory (wordBits z d Native.copies)) (T : ℝ) :
    let x := stockQuotes (z:=z) (d:=d) (k:=k) phase payload signed base raw
    ((Fintype.card (Fin (2^z) × Fin (2*rounds d+1)):ℝ) ≤
      ∑v,∑a : Fin k×Bool,phase.time*(rise phase.M (x (.inr (v,a)))/T)^2) ↔
    ((Fintype.card (Tile z d):ℝ) ≤ ∑ v,∑ a : Fin k×Bool,
      phase.time*(rise phase.M (phase.quote signed (stockBits base k raw v a))/T)^2) := by
  dsimp only
  let q (v : Fin (2^z) × Fin (2*rounds d+1)) := ∑a : Fin k×Bool,
    phase.time*(rise phase.M (stockQuotes (z:=z) (d:=d) (k:=k) phase payload signed base raw (.inr (v,a)))/T)^2
  have sums := (tileAddress z d).sum_comp q
  have cards := Fintype.card_congr (tileAddress z d)
  change ((Fintype.card (Fin (2^z) × Fin (2*rounds d+1)):ℝ) ≤ ∑v,q v) ↔
    ((Fintype.card (Tile z d):ℝ) ≤ ∑v,q (tileAddress z d v))
  rw [sums,cards]

/-- The precise integer mark words satisfy the coverage lower bound immediately
from the measured commodity energy. The table and the payload/signed kinds are
arbitrary installed banks. -/
theorem coverage_of_motion {z d k : ℕ} (phase : PhasePrice) (payload signed base : ℕ)
    (table : Bank) (raw : Memory (wordBits z d Native.copies)) (T : ℝ) (hk : 0<k) (pos : 0<T)
    (time : 0≤phase.time) (early : phase.time≤1)
    (fit : ∀v a,stockBits base k raw v a<table.size)
    (cap : ∀v a,rise phase.M (phase.quote signed (stockBits base k raw v a))≤1) :
    let x := stockQuotes (z:=z) (d:=d) (k:=k) phase payload signed base raw
    (Fintype.card (Fin (2^z) × Fin (2*rounds d+1)):ℝ) ≤
      ∑v,∑a : Fin k×Bool,phase.time*(rise phase.M (x (.inr (v,a)))/T)^2 →
    T^2/(4*k)*((permutationFabric z d).shapes.length*(2:ℝ)^z) ≤
      ∑t,∑j,((strataAt base table k phase T signed raw t j).card:ℝ) := by
  intro _ energy
  exact measured_coverage_at base table k hk phase T signed raw pos time early fit cap
    ((measured_motion (k:=k) phase payload signed base raw T).mp energy)

end
end Hierarchy.ProtocolRAM.PurchaseCT

end OAI
