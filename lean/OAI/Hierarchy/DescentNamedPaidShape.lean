import OAI.Hierarchy.DescentTerminalCalibratedShape
import OAI.Hierarchy.DescentNamedLeafCalibration
import OAI.Hierarchy.DescentNamedPublishedExterior

namespace OAI
/-! # The public terminal pool of the named compiler consists of complete chip bins -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter
open DescentTerminalGraphVolume DescentTerminalBinPack Catalyst CatalystSubstitution
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F)
variable (t J f g resetRate M τ height n h C : ℕ)
local notation "tailBits" => tail τ J
local notation "S" => stageNumbers G t J f g resetRate M tailBits
local notation "k" => groupBits t J (S).hostGain (S).capGain (cutRate t f g)
local notation "W" => NativeBranch.binLimit («k»:=k) S
local notation "j" => Nat.clog 2 (NativeBranch.localLimit G S)
local notation "u" => G.b^(t*J)*G.b
local notation "q" => 2^j*u
local notation "piece" => height/(16*(q*W))
local notation "p" => W*piece
local notation "rest" => (S).groupWidth k tailBits 0+k-2*j
local notation "E" => Fintype.card (Port P X.width)
local notation "H" => (S).hostSize (S).length
local notation "s" => (S).firstWidth G.b p
local notation "rawRows" => terminalRawRows X G S p q n h C f g
local notation "poolRows" => terminalPool X G S p q W n h C f g
local notation "wordBudget" => terminalWireBudget X G S p n h C f g

variable (template : DescentTerminalCompiledPrefix.Shape) (headerRows : ℕ) (Mpos : 0<M)

local notation "capped" => calibrated_shell X G t J f g resetRate M τ height n h C template headerRows Mpos
local notation "binsAt" => calibratedBins X G t J f g resetRate M τ height n h C

/-- The existing calibrated leaf buys exactly the rows already allocated in this shell. -/
theorem buy_calibrated_shell :
    buyLeafRows («W»:=W) («q»:=q) («piece»:=piece) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g)
      X G S capped = capped := rfl

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
