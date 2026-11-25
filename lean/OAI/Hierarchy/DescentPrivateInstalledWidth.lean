import OAI.Hierarchy.DescentDepotSetup
import OAI.Hierarchy.DescentPrivateDepotNames

namespace OAI
/-! # Shared fully mounted ordinary date and the actual budgeted lane width -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentRawCablePanel.DepotRAM DescentHostDegree DescentPackedPrivateSum DescentRawCablePanel DescentSIMDLookup
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k j i z₀ D₀ z D wire hist bw : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist}
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink source he T c n target)


namespace OrdinaryLink
variable (shortDigit profile : ℕ)
local notation "A" => source.placement
local notation "fmt" => depotShape ticket shortDigit
local notation "zfmt" => DescentPacking.PackedMatch.Local.shape (2^k) (A).degree (2*(A).cap) profile

def installedDonorWidth := max (depotWidth ticket shortDigit) (max (Fresh.laneWidth fmt zfmt) (2*totalBits fmt+1))

theorem installed_donor_books (hosts payload : ℕ) :
    let amount:=installedDonorWidth ticket shortDigit profile
    let M:=lanes payload amount
    Setup.words fmt zfmt (2^(k+1)) hosts (S.groupCount i) M amount ≤
      2*(hosts*chunks (S.groupCount i) M)+(2*Binary.count fmt+3+2^(k+1))*2^(payload/2) :=
  Setup.capacity fmt zfmt (2^(k+1)) hosts (S.groupCount i) _ payload ((le_max_right ..).trans (le_max_right ..))
    ((le_max_left ..).trans (le_max_right ..))

theorem installed_donor_widths :
    let amount:=installedDonorWidth ticket shortDigit profile
    depotWidth ticket shortDigit≤amount ∧ Fresh.laneWidth fmt zfmt≤amount ∧ 2*totalBits fmt+1≤amount :=
  ⟨le_max_left ..,(le_max_left ..).trans (le_max_right ..),(le_max_right ..).trans (le_max_right ..)⟩

end OrdinaryLink
end
end Hierarchy.DescentSixParty.Chronology

end OAI
