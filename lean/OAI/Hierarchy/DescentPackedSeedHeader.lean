import OAI.Hierarchy.DescentSeedSiteIndex
import OAI.Hierarchy.DescentSeedHeaderCharge
import OAI.Hierarchy.DescentSeedPackedHeaderNumbers
import OAI.Hierarchy.DescentSeedSiteGeometry
import OAI.Hierarchy.DescentPackedRegroup
import OAI.Hierarchy.DescentTerminalSeedSelectors
import OAI.Hierarchy.DescentPackedBallotHeader

namespace OAI
/-! # Read the accepted seed choice from its packed census slot -/
namespace Hierarchy.DescentPackedSeed
open DescentSeedRoot DescentInitialHost
open ThreeFlat Routing Catalyst Diagonal TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization
open scoped BigOperators Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p) {R s : ℕ}

theorem selected_slot (w : ℕ) (c : (initialGroup X R s).Choice) (fits : s<2^w)
    (room : 0 < multiplicity w s) (j : Fin R) (v : Old X) (pat : LocalPattern X v) :
    let rank:=finProdFinEquiv (j,code X pat)
    let a:=DescentSIMDLookup.position ((Fintype.equivFin _) v) rank room
    DescentSIMDLookup.digit (digitsNeeded s) (DescentSIMDLookup.lane rank room).val
      (initialMemory (headerWords X R s w) (base X w (selectBit X w c))
        (publicWords X+(DescentSIMDLookup.row _ _ _ a).val)).val=(c j (.inl v) pat).val :=
  (slot_read X w (selectBit X w c) room j v pat).trans (raw_select X fits c _)

end
end Hierarchy.DescentPackedSeed

end OAI
