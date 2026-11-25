import OAI.Hierarchy.DescentOriginalNumberVolume

namespace OAI
/-! # A structural polynomial for the original donor and number sheets -/
namespace Hierarchy.DescentDatedAddressBook.CandidateSheets.OriginalInputs
open DescentResetOriginalDonors CandidateFront
noncomputable section
variable {s : CandidateSheets} (u : s.OriginalInputs)

private def panelCost (n x v : ℕ) :=
  339+4096*volumeFactor n x+
    (4+n*(4+(2*(v+12)+4)))+7*(15+n*(11+4*(v+12)))

private theorem panel_mono {a b c A B C : ℕ} (ha : a≤A) (hb : b≤B) (hc : c≤C) :
    panelCost a b c ≤ panelCost A B C := by
  unfold panelCost volumeFactor
  gcongr

private theorem static_mono {a b : ℕ} (h : a≤b) : staticCost a ≤ staticCost b := by
  unfold staticCost
  gcongr

private theorem format_mono {x q t p k u X Q T P K U c C : ℕ}
    (hx : x≤X) (hq : q≤Q) (ht : t≤T) (hp : p≤P) (hk : k≤K) (hu : u≤U) (hc : c≤C) :
    formatFactor x q t p k u 64 c ≤ formatFactor X Q T P K U 64 C := by
  dsimp only [formatFactor,staticCost]
  gcongr

/-- The argument bounds only the structural fields of the named original-number compiler. -/
theorem numberFactor_polynomial (U V n : ℕ)
    (coords : s.coordinate.count≤n) (donors : s.donorSlots≤n)
    (blocks : s.blocks≤n) (contacts : s.contacts≤n) (stems : u.stems≤n)
    (privates : s.privates≤n) (signed : u.signedSlots≤n) (hu : U≤n) (hv : V≤n) :
    u.numberFactor U V 64 ≤ 100000000*(n+1)^5 := by
  have coeff : s.originalDonors.coefficient V ≤
      panelCost (2*n) n n + panelCost (2*n) n n + panelCost n n n := by
    change panelCost (2*s.donorSlots) s.blocks V + panelCost (2*s.donorSlots) s.blocks V +
      panelCost s.donorSlots s.blocks V ≤ _
    have twice := panel_mono (Nat.mul_le_mul_left 2 donors) blocks hv
    exact Nat.add_le_add (Nat.add_le_add twice twice) (panel_mono donors blocks hv)
  let c := (n+1)*2+1
  have fee : donorFactor s ≤ c := by unfold donorFactor c; omega
  have format := format_mono blocks contacts stems privates signed hu fee
  calc
    u.numberFactor U V 64 ≤ staticCost (3+n)+staticCost 6+staticCost 6+
        (panelCost (2*n) n n + panelCost (2*n) n n + panelCost n n n)+
        formatFactor n n n n n n 64 c + staticCost n + staticCost 3 := by
      unfold numberFactor
      have first := static_mono (Nat.add_le_add_left coords 3)
      have last := static_mono privates
      omega
    _ ≤ _ := by
      unfold formatFactor panelCost staticCost volumeFactor c
      ring_nf
      omega

end
end Hierarchy.DescentDatedAddressBook.CandidateSheets.OriginalInputs

end OAI
