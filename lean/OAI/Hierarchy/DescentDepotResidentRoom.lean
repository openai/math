import OAI.Hierarchy.DescentDepotRoom
import OAI.Hierarchy.DescentDepotKeep

namespace OAI
/-! # Authentic resident-source addresses and the common ordinary-date geometry -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Setup
open DescentPackedZip DescentSIMDLookup DescentPacking.PackedMatch DescentPacking.PackedMatch.Local DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical
noncomputable section
variable {w : ℕ} (s : DepotRAM.Shape) (z : DescentPacking.PackedMatch.Shape) (K H G M unit base : ℕ)
local notation "second" => base+DescentSIMDLookup.Book.words (totalBits s) H G M
local notation "num" => Binary.count s*(2*2^(unit*M))
local notation "freshBase" => second+num
local notation "roof" => base+2*(words s z K H G M unit+1)

def sources (R : Resident.Sources s K) (top born : Bank) : Resident.Sources s K :=
  { Binary.fields s M unit second R with fresh:=Fresh.Book.bank s z K H G M freshBase top born }

variable (out : ℕ) (R : Resident.Sources s K) (top born : Bank)
local notation "real" => sources s z K H G M unit base R top born
local notation "issued" => Resident.fields s z real H G M
local notation "T" => Binary.joints s M unit second

/-- Only the genuinely dynamic source banks have independent layout fields. -/
theorem room (large : 2*totalBits s+1≤unit) (stamped : roof≤out) (word : out<2^w)
    (bits : ∀i,(R.signed i).Fits w out) (terrain : R.terrain.Fits w out)
    (peers : Accessible R.peers R.owner H G M w out)
    (ranks : DescentHaloPackedRebase.Fits R.ranks H G M w out)
    (hubs : DescentHaloPackedRebase.Fits R.hubs H G M w out)
    (topRead : top.Fits w out) (bornRead : born.Fits w out)
    (topCount : (K*H)*chunks G M≤top.size) (bornCount : (K*H)*chunks G M≤born.size)
    (small : SixBirths.width z M≤w) :
    Resident.Fits s z real H G M w out ∧ FitsInputs s T issued M out w := by
  have binary : freshBase≤out:=by unfold words Binary.words at stamped;omega
  have nativeSigned:=Binary.cable_room s M unit second out large binary word R.signed bits
  have e (i : Fin (s.degree+1)) : (Owners.expression R.peers R.owner H i).Fits w out := by
    cases i using Fin.cases with
    | zero => exact ⟨peers.source,trivial⟩
    | succ j => exact peer_fits R.peers R.owner out peers j
  have nativeOwner:=Binary.owner_room s M unit second out large binary word _ e
  have computed:=fresh_room s z K H G M unit base top born R.terrain terrain topRead bornRead topCount bornCount small stamped word
  refine ⟨⟨nativeSigned,nativeOwner,peers,peers.srcRoom,peers.source,ranks,hubs,computed⟩,?_⟩
  refine Binary.gather_room s M unit second out large binary word issued terrain ?_ ?_ ?_ ?_ ?_
  · exact Gather.fits _ _ _ nativeSigned _
  · exact Gather.fits _ _ _ nativeOwner _
  · exact DescentHaloPackedRebase.context_fits _ _ ranks
  · exact DescentHaloPackedRebase.context_fits _ _ hubs
  · exact Fresh.fits s z _ _ computed

theorem immutable {B prof C pad scale : ℕ} (m : Memory w) (live : Binary.Installed s M unit second m)
    (fresh : Fresh.Fixed (H:=H) (G:=G) (M:=M) s z (Fresh.Book.bank s z K H G M freshBase top born) B prof C pad scale m) :
    Resident.Immutable (H:=H) (G:=G) (M:=M) s z real B prof C pad scale m := ⟨live.2.1,live.2.2.1,fresh⟩

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Setup

end OAI
