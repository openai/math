import OAI.Computability.BorderVNP.ParseBatchPrewire

/-! # Bit volume of the interior-wired physical verifier -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatch.Prewire

open VPVNP BooleanTranscript TeamContraction
open scoped Classical

variable {X Y I W J : Type} [Fintype X] [Fintype Y] [Fintype I] [Fintype W] [Fintype J] {s : ℕ}

/-- Rewiring keeps all gate and weight sites. When private edge names and public
slots fit in the original input count, the physical bit volume can only decrease. -/
theorem rewire_volume (f : X → (Y ⊕ I) ⊕ Bool) (c : BooleanTranscript.Circuit (X ⊕ W) s)
    (w : J → W) (h : Fintype.card Y + Fintype.card I ≤ Fintype.card X) :
    (BooleanLayout.layout (circuit (projection f) c) (fun j => Sum.inr (w j))).network.bitVolume ≤
      (BooleanLayout.layout c w).network.bitVolume := by
  unfold Crossing.Network.bitVolume
  rw [Layout.volume_eq,Layout.volume_eq, Layout.uses_eq, Layout.uses_eq]
  simp only [BooleanLayout.layout, Layout.ofArguments, BooleanLayout.Hidden, Fintype.card_sum]
  omega

/-- The actual frame, boundary and comparator variables of one physical team
fit in its interior slot budget. No edge is introduced for a zero clamp. -/
theorem tape_edges_le (r k w e W : ℕ) (hr : 0 < r) :
    Fintype.card (Wires.Edge r k w e W) ≤ r * Wires.innerWidth r k w e W := by
  let d := Nat.clog 2 r
  have hc := (TeamSorting.padding_lt_twice hr).le
  change 2^d ≤ 2*r at hc
  have h₁ := Nat.mul_le_mul_right (Wires.frameWidth k w) (Nat.sub_le r 1)
  have h₂ := Nat.mul_le_mul_right (5*W) ((Nat.sub_le (2^d) 1).trans hc)
  have h₃ := Nat.mul_le_mul_left (RAMLayout.layerCount d)
    (Nat.mul_le_mul_right (RAMLayout.blockBits (2^e) W) hc)
  simp only [Wires.Edge, Wires.SortEdge, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin]
  change (r-1)*Wires.frameWidth k w +
    ((2^d-1)*(5*W) + Fintype.card (RAMLayout.Layer d)*(2^d*RAMLayout.blockBits (2^e) W)) ≤ _
  rw [Fintype.card_congr (RAMLayout.layerEquiv d), Fintype.card_fin]
  refine (Nat.add_le_add h₁ (Nat.add_le_add h₂ h₃)).trans ?_
  change r*Wires.frameWidth k w + (2*r*(5*W) + RAMLayout.layerCount d*(2*r*RAMLayout.blockBits (2^e) W)) ≤
    r*(2*Wires.frameWidth k w + 2*(10*W + TeamTapeInputRoute.comparisonSize d e W))
  simp only [RAMLayout.layerCount, RAMLayout.blockBits, TeamTapeInputRoute.comparisonSize]
  nlinarith [Nat.zero_le (r * Wires.frameWidth k w),
    Nat.zero_le ((d+1).choose 2 * r * 2^e * W), Nat.zero_le (r * W)]

/-- The original slot count covers the active public leaves and all shared
private variables before any routing, with the actual padded input width. -/
theorem card_public_private_le {R r t d link inner n : ℕ} {Edge : Type} [Fintype Edge]
    (G : Wiring R r t d link inner n Edge) (he : Fintype.card Edge ≤ r*inner) :
    Fintype.card (Fin r × Fin (publicWidth G)) + Fintype.card Edge ≤ Fintype.card (Fin r × Fin n) := by
  simp only [Fintype.card_prod,Fintype.card_fin]
  exact (Nat.add_le_add_left he _).trans ((Nat.mul_add ..).symm.le.trans
    (Nat.mul_le_mul_left r G.fits))

end ParseBatch.Prewire

end BorderVNP
end Computability
end OAI
