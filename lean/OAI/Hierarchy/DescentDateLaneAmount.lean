import OAI.Hierarchy.DescentNamedDonorCode
import OAI.Hierarchy.DescentPrivateDonorUniform

namespace OAI
/-! # The calendar compiler and the donor tariff select the same packing pitch -/
namespace Hierarchy.DescentSixParty.Chronology.DonorDate
open DescentCompiler DescentCompiler.TerminalScale DescentPacking.PackedMatch.Local.Stage.Dated
open DescentSIMDLookup
set_option maxRecDepth 4096
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)

theorem atDate_amount (gain k i p : ℕ) :
    let d:=atDate G S gain k i p
    d.amount=donorAmount k d.degree d.cap G.b G.C G.k := by rfl

theorem seed_lanes (gain k p payload : ℕ) :
    let d:=atDate G S gain k 0 p
    lanes payload d.amount=lanes payload (donorAmount k d.degree 256 G.b G.C G.k) := by rfl

end Hierarchy.DescentSixParty.Chronology.DonorDate

end OAI
