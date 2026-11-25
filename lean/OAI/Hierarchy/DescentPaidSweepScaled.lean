import OAI.Hierarchy.DescentPaidSweepWordVolume
import OAI.Hierarchy.DescentPaidSweepHeldBill

namespace OAI
/-! # The actual funded and occupied publication at occupied, unequal group pitches -/
namespace Hierarchy.DescentPaidResidentCount.Sweep.HeldRepacked
open DescentSIMDLookup DescentOrdinaryAtomFieldRAM
variable (base H G old M k paths cap b n p t : ℕ)
local notation "B₀" => 2^k
local notation "D₀" => paths*B₀
local notation "cBits" => (b*D₀+b)*M

theorem bill_expanded : bill base H G old M k paths cap b n p t=
    WordVolume.expanded B₀ D₀ p t (H*chunks G old) (H*chunks G M)
      ((Overlap.pieces G old M+1)*(old+1)*2^(b*old)) (2^cBits)
      (2^maskBits D₀ cap n M) (2^sumBits D₀ cap b M) :=by
  simp only [bill,RoleCounts.Repitch.bill,DescentVenueSlabs.ExprInputs.tariff,RoleCounts.Repitch.shape,
    RoleCounts.Repitch.count,RoleCounts.layout,RoleCounts.Layout.tableWords,RoleCounts.Layout.romBits,
    RoleCounts.Layout.rows,RoleCounts.Layout.donors,Overlap.rows,rowCount,tableBill,columnBill,
    WordVolume.expanded,WordVolume.oldCost,WordVolume.newCost,WordVolume.fixedCost]
  ring

/-- A linear charge at the word level for all physical host/group rows, plus one
    independent sublinear dictionary term at the chosen public upper height. -/
theorem scaled (h w ratio u₀ u₁ : ℕ) (word : w≤ratio*h)
    (source : old≤h) (target : M≤h) (oldBits : b*old≤h/2)
    (census : cBits≤h/2) (masks : maskBits D₀ cap n M≤h/2) (sums : sumBits D₀ cap b M≤h/2)
    (fill₀ : h≤old*u₀) (fill₁ : h≤M*u₁) :
    bill base H G old M k paths cap b n p t*w≤
      ratio*(WordVolume.rowRate B₀ D₀ p t*(H*h+H*G*(u₀+u₁))+
        WordVolume.tableRate B₀ D₀ p t*((h+1)^2*2^(h/2)*h)) :=by
  rw [bill_expanded]
  exact WordVolume.charged B₀ D₀ p t H G old M b cBits (maskBits D₀ cap n M) (sumBits D₀ cap b M)
    h w ratio u₀ u₁ word source target oldBits census masks sums fill₀ fill₁

end Hierarchy.DescentPaidResidentCount.Sweep.HeldRepacked

end OAI
