import OAI.Hierarchy.DescentDonorGatherRAM
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # The registers retained after the actual private donor gather -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (s : Shape) {w H J M : ℕ}

/-- The end of the actual donor program preserves the whole genuine gathered
input at its previous source bank while writing the charge to its output. -/
theorem retained (t : Tables6) (f : Fields) (rom : Banks) (out : ℕ)
    (fit : FitsInputs s t f M rom.source.base w)
    (finish : DescentSIMDLookup.Fits rom (totalBits s) (outputBits s) M H J w out)
    (x : Fin H→Fin J→Parts s) (m : Memory w) (common : Fixed s t M m) (sources : Loaded s f x M m) :
    Reads rom.source (fun h j=>combine s (x h j)) M (after t f rom out H J M m) := by
  intro p
  let length:=H*chunks J M
  have prior : rom.source.base+(row H J M p).val<out:=
    ((Nat.add_lt_add_left (row H J M p).isLt _).trans_le (Nat.add_le_add_left finish.srcSize _)).trans_le finish.source.2.2
  have real:=gathered s t f rom.source.base fit x m common sources p
  have before : after t f rom out H J M m (rom.source.base+(row H J M p).val)=
      image rom.source.base (H*chunks J M) (gather t f) m (rom.source.base+(row H J M p).val) :=by
    simp [after,image,fillSegment,Nat.not_le.mpr prior]
  exact before.trans ((ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row H J M p)).trans real)

end
end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
