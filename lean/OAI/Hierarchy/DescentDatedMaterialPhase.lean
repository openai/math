import OAI.Hierarchy.DescentDatedOrdinaryMaterial
import OAI.Hierarchy.DescentMaterialProgram

namespace OAI
/-! The ordinary cross-rack observations run between the original donor and the successor signed banks. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedColony
open DescentSharedCableNames DescentHaloPackedRebase DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
set_option quotPrecheck false
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
def materialPitch := (2^(v.k+1)-1)*(2^DescentHostDegree.packExponent 20 v.stage.Δ+2)
def materialFormat : DepotRAM.Material.Setup :=
  ⟨v.profile,v.gadget.b,v.k,DescentHostDegree.gainExponent 20 v.stage.Δ,
    2^DescentHostDegree.packExponent 20 v.stage.Δ+2,v.materialPitch,v.signed.fieldBits⟩
def materialProgram : MaterialProgram := ⟨v.material,fmt,v.materialFormat⟩
def rankHeader (base : ℕ) (reverse : Bank) := v.materialProgram.rankHeader base reverse
def materialCharts (base w : ℕ) : NativePhase w := v.materialProgram.materialCharts base w
def materialJoin (base : ℕ) (parts reverse : Bank) (w : ℕ) := v.materialProgram.materialJoin base parts reverse w
def joinBank (base : ℕ) := v.materialProgram.joinBank base
def materialSheets (base w : ℕ) := v.materialProgram.materialSheets base w
def materialJob (base : ℕ) : Overlap.Job := v.materialProgram.materialJob base
def materialMaps (base w : ℕ) := v.materialProgram.materialMaps base w
def materialAt (base : ℕ) (parts reverse : Bank) (w : ℕ) : NativePhase w :=
  v.materialProgram.materialAt base parts reverse w
def materialPhase (floor : ℕ) (parts reverse : Bank) (w : ℕ) :=
  v.materialAt (v.materialStart floor) parts reverse w

theorem material_phase_clock (floor : ℕ) (parts reverse : Bank) (w : ℕ) :
    let b:=v.materialStart floor
    (v.materialPhase floor parts reverse w).ticks=
    ((((v.materialCharts b w).ticks+(v.materialJoin b parts reverse w).ticks)+(v.materialSheets b w).ticks)+
      ((v.materialJob b).phase ((e).overlapStart b) w).ticks)+(v.materialMaps b w).ticks :=rfl

/-- The existing nine fields are normalized once per old group width. Each output socket reuses a slice. -/
def receivedBank (base : ℕ) (j : Fin (DepotRAM.Material.Sheets.count fmt)) : Bank :=
  v.materialProgram.receivedBank base j

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
