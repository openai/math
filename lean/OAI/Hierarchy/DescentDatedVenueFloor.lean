import OAI.Hierarchy.DescentDatedStageVenue
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Reserving more space after the actual dated inputs -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentPackedColony DescentColonies DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] {u : ℕ} {bits : P→ℕ} {W : MarkedWorld F u P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z D wire s H w : ℕ}
    (r : Reached W G q ε S k age z D wire s) (wide : Fintype.card r.V≤H)
    (i : Dated.Operands) (M countBits floor : ℕ) (rs : Fin H→Fin D→Option (Fin H))
local notation "g" => S.groupCount age

theorem stageVenue_mono (m : Memory w) {next : ℕ} (later : floor≤next)
    (old : stageVenue r wide i M countBits floor rs m) :
    stageVenue r wide i M countBits next rs m :=by
  rcases old with ⟨ac,roster,actors,wires,hubs,slots,hub,atomFits,atoms⟩
  have grow {B : Bank} (h : B.Fits w floor) : B.Fits w next := ⟨h.1,h.2.1,h.2.2.trans later⟩
  refine ⟨?_,roster,actors,wires,grow hubs,slots,hub,?_,atoms⟩
  · exact ⟨fun j=>grow (ac.ids j),ac.idsRoom,grow ac.roster,ac.rosterRoom,
      grow ac.offsets,ac.offRoom,grow ac.chunks,ac.chunkRoom,grow ac.source,ac.srcRoom⟩
  · intro x
    exact ProtocolRAMGeneratedWrite.fits_mono _ later (atomFits x)

end
end Hierarchy.DescentSixParty

end OAI
