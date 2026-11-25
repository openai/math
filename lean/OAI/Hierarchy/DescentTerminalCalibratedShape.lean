import OAI.Hierarchy.DescentTerminalShapeData
import OAI.Hierarchy.DescentTerminalPublicRows
import OAI.Hierarchy.DescentNativeSocketScale

namespace OAI
/-! # The whole-bin capacities of the genuine terminal at the selected public schedule -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale
open DescentTerminalGraphVolume Catalyst
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

/-- The original certified row budget is rounded down to whole bins because its
use was certified in whole bins in the graph purchase proof. -/
def calibratedBins := rowBudget p q W wordBudget ((S).copies*s*E) H 3 / W

variable (template : DescentTerminalCompiledPrefix.Shape) (headerRows : ℕ) (Mpos : 0<M)

include Mpos in
theorem calibrated_hosts_positive : 0<H := by
  change 0<M*(2^(_ : ℕ)*2^(_ : ℕ))^(_ : ℕ)
  positivity

/-- Preserve the counter geometry from the dated prefix. The public sort uses
the initial pin count, and all three chip scans have identical row capacity. -/
def calibrated_shell : DescentTerminalCompiledPrefix.Shape :=
  let ext := Branch.exteriorShape template E j rest s rawRows headerRows H
    (calibrated_hosts_positive G t J f g resetRate M τ Mpos)
  {ext with terminal:={ext.terminal with rows:=poolRows, pool:=poolRows, leaves:=poolRows}}

local notation "capped" => calibrated_shell X G t J f g resetRate M τ height n h C template headerRows Mpos
local notation "binsAt" => calibratedBins X G t J f g resetRate M τ height n h C

theorem calibrated_shell_geometry :
    (capped).sites=H ∧ (capped).terminal.rows=binsAt*W ∧ (capped).terminal.pool=binsAt*W ∧
    (capped).terminal.leaves=(capped).terminal.pool ∧
    (capped).terminal.plane.publicRows=E*2^(j+rest) ∧
    (capped).terminal.plane.rawRows=rawRows := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
