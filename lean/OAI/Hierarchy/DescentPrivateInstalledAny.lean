import OAI.Hierarchy.DescentDepotResidentRoom
import OAI.Hierarchy.DescentPrivateGatherPhase

namespace OAI
/-! # Exact ordinary date on arbitrary input values at the full mounted layout -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Setup
open DescentPacking.PackedMatch DescentPacking.PackedMatch.Local DescentPackedZip DescentSIMDLookup DescentPackedColony
open DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM ThreeFlat.RAM
open scoped Classical
noncomputable section
variable {w out : ℕ} (s : DepotRAM.Shape) (z : DescentPacking.PackedMatch.Shape)
variable (K H G M unit base B prof C pad scale b seats : ℕ) (src top born : Bank) (R : Resident.Sources s K)
local notation "allWords" => words s z K H G M unit
local notation "boot" => phase s z K H G M unit base B prof C pad scale b seats w
local notation "rom" => DescentSIMDLookup.Book.banks base (totalBits s) H G M src
local notation "second" => base+DescentSIMDLookup.Book.words (totalBits s) H G M
local notation "inputs" => Resident.fields s z (sources s z K H G M unit base R top born) H G M
local notation "tabs" => Binary.joints s M unit second
local notation "gather" => DepotRAM.phase tabs inputs rom out H G M w

theorem date_any (geometry : NativePhase w) (total : ∀m,geometry.Runs m)
    (large : 2*totalBits s+1≤unit) (stamped : base+2*(allWords+1)≤ src.base)
    (count : H*chunks G M≤ src.size) (gate : src.base+src.size≤out)
    (endAt : out+H*chunks G M<2^w) (key : M*max (totalBits s) (outputBits s)≤w/2)
    (signed : ∀j,(R.signed j).Fits w src.base) (terrain : R.terrain.Fits w src.base)
    (near : Accessible R.peers R.owner H G M w src.base)
    (ord : DescentHaloPackedRebase.Fits R.ranks H G M w src.base)
    (hub : DescentHaloPackedRebase.Fits R.hubs H G M w src.base)
    (topSpace : top.Fits w src.base) (bornSpace : born.Fits w src.base)
    (oldRoom : (K*H)*chunks G M≤top.size) (birthRoom : (K*H)*chunks G M≤born.size)
    (wide : SixBirths.width z M≤w) (m : Memory w) :
    (((boot).seq geometry).seq gather).Runs m := by
  have before : src.base<2^w:=by omega
  have first : (boot).Runs m := (mount s z K H G M unit base B prof C pad scale b seats src top born m large
    (show base+allWords<2^w by omega)).1
  have gathered:=(room s z K H G M unit base src.base R top born large stamped before signed terrain near ord hub
    topSpace bornSpace oldRoom birthRoom wide).2
  have fit:=(lookup_room s z K H G M unit base src stamped count gate endAt key).1
  intro pcs regs pubs cpu
  exact NativePhase.seq_runs _ _ m (NativePhase.seq_runs _ _ m first (total _))
    (DepotRAM.phase_any s tabs inputs rom out H G M w gathered fit _) cpu

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Setup

end OAI
