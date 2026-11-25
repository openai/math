import OAI.Hierarchy.DescentSixPartyGadget
import OAI.Hierarchy.DescentResetPublicDepth
import OAI.Hierarchy.DescentResetSplicePrice
import OAI.Hierarchy.DescentGrainCalendar
import OAI.Hierarchy.DescentTerminalCalibratedRowArithmetic
import OAI.Hierarchy.DescentPublicDegreeNumbers
import OAI.Hierarchy.Catalyst
import OAI.ThreeFlat.Routing.CallPoolBudget

namespace OAI
/-! # Public sizes of the purchased terminal wire and bin banks -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentResetInvoice Catalyst DescentTerminalGraphVolume
open ThreeFlat.Routing
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
local notation "E" => Fintype.card (Port P X.width)

def terminalWireBudget (p n h C f g : ℕ) : ℕ :=
  integralFrontier S.epochPower S.initialSites (S.copies*S.firstWidth G.b p) E
    ⌈258*reentryRate h C+reentryExteriorRate h C 256 (GroupStage.depthBound (atRound S.rounds) n f g)⌉₊

def terminalPool (p q W n h C f g : ℕ) : ℕ :=
  rowBudget p q W (terminalWireBudget X G S p n h C f g) ((S.copies*S.firstWidth G.b p)*E)
    (S.hostSize S.length) 3 / W * W

def terminalRawRows (p q n h C f g : ℕ) :=
  poolBatchCount (terminalWireBudget X G S p n h C f g) (q*p)

def terminalBinCount (p q W n h C f g : ℕ) :=
  rowBudget p q W (terminalWireBudget X G S p n h C f g) ((S.copies*S.firstWidth G.b p)*E)
    (S.hostSize S.length) 3 / W

theorem terminal_pool_eq (p q W n h C f g : ℕ) :
    terminalPool X G S p q W n h C f g=terminalBinCount X G S p q W n h C f g*W:=rfl

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
