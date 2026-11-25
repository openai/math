import OAI.Hierarchy.DescentDepotZipInstall
import OAI.Hierarchy.DescentDonorFreshTables
import OAI.Hierarchy.DescentPrivateFreshDepot
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # A finite public opcode block mounts the fresh and binary donor books, with full frames -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Binary
open DescentPackedZip DescentPacking.PackedMatch DescentPacking.PackedMatch.Local DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentSixParty.Chronology ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (s : DepotRAM.Shape) (z : DescentPacking.PackedMatch.Shape) (K H G M unit : ℕ)
local notation "bin" => count s*(2*2^(unit*M))
local notation "isolated" => Fresh.Book.physicalSize s z K H G M
local notation "width" => Fresh.laneWidth s z

def words := bin+isolated

variable (base B prof C pad scale : ℕ)
local notation "window" => base+bin
local notation "A" => Book.install (menu s) unit M
local notation "next" => Fresh.Book.install s z K H G M
local notation "boot" => Book.image (menu s) unit M base
local notation "fresh" => Fresh.Book.image s z K H G M window B prof C pad scale

def phase (w : ℕ) : NativePhase w :=
  ⟨(A w base).seq (next w window B prof C pad scale),8+10*words s z K H G M unit,
    fun m=>fresh (boot m),cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@DescentStaticWordColumn.cheap _ _ _ _)⟩
local notation "date" => phase s z K H G M unit base B prof C pad scale

theorem mount {w : ℕ} (top born : Bank) (m : Memory w) (wide : 2*totalBits s+1≤unit)
    (room : base+words s z K H G M unit<2^w) :
    (date w).Runs m ∧ Installed s M unit base ((date w).image m) ∧
      Fresh.Fixed (H:=H) (G:=G) (M:=M) s z (Fresh.Book.bank s z K H G M window top born)
        B prof C pad scale ((date w).image m) ∧
      ∀a,a<base ∨ base+words s z K H G M unit≤a → (date w).image m a=m a := by
  have span : window+isolated<2^w := by simpa only [words,Nat.add_assoc] using room
  have supported : ∀i,(menu s i).left+(menu s i).right≤unit := fun i=>(Binary.width s ((ordinal s).symm i)).trans wide
  obtain ⟨first,tables,safe,_⟩:=Book.mount (menu s) unit M base m supported (show window<2^w by omega)
  obtain ⟨second,pages,after⟩:=Fresh.Book.mount s z K H G M w window B prof C pad scale top born (boot m) span
  have retained:=Book.retained (menu s) unit M base (fresh (boot m)) (boot m) supported tables
    (fun a _ ha=>after a (.inl ha))
  refine ⟨?_,installed_of_all s M unit base _ retained,pages,?_⟩
  · have time : 8+10*words s z K H G M unit=(4+10*bin)+(4+10*isolated) := by unfold words;ring
    change ((A w base).seq (next w window B prof C pad scale)).Exec m (fresh (boot m)) (8+10*words s z K H G M unit)
    rw [time]
    intro P R K₀ mach pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then first second mach pc reg pub exit rom advice cfg raw enter same
  · intro a outside
    unfold words at outside
    exact (after a (by omega)).trans (safe a (by omega))

theorem names (w : ℕ) :
    DescentStaticWordColumn.names (date w).program=15*(words s z K H G M unit+2) := by
  simp only [phase,Book.install,Fresh.Book.install,DescentStaticWordColumn.names_seq,
    DescentStaticWordColumn.names_mount,words]
  ring

/-- Every table is shared across the whole date. Only the actual tail mask
costs one word for each occupied host and group batch. -/
theorem capacity (payload : ℕ) (freshFits : width≤unit) :
    words s z K H G (lanes payload unit) unit≤
      H*chunks G (lanes payload unit)+(2*count s+2+K)*2^(payload/2) := by
  let M₀:=lanes payload unit
  have lane : unit*M₀≤payload/2 := by simpa [M₀,Nat.mul_comm] using lanes_fit payload unit
  have natural : rawBits s*M₀≤payload/2 :=
    (Nat.mul_le_mul_right M₀ (show rawBits s≤unit by unfold Fresh.laneWidth at freshFits;omega)).trans lane
  have topo : SixBirths.topology z M₀≤payload/2 :=
    (Nat.mul_le_mul_right M₀ (show z.outputBits≤unit by unfold Fresh.laneWidth at freshFits;omega)).trans lane
  have strong : Fresh.Book.bits s z M₀≤payload/2 := by
    have pre: Fresh.Book.bits s z M₀=width*M₀ := by
      unfold Fresh.Book.bits Fresh.laneWidth SixBirths.topology SixBirths.width
      ring
    rw [pre];exact (Nat.mul_le_mul_right M₀ freshFits).trans lane
  have ordinary:=Nat.mul_le_mul_left (count s*2) (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) lane)
  have raw:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) natural
  have old:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) topo
  have last:=Nat.mul_le_mul_left K (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) strong)
  change count s*(2*2^(unit*M₀))+(H*chunks G M₀+(2^(rawBits s*M₀)+(2^(SixBirths.topology z M₀)+K*2^(Fresh.Book.bits s z M₀))))≤_
  nlinarith only [ordinary,raw,old,last]

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Binary

end OAI
