import OAI.Hierarchy.DescentNamedOriginalInitialPrice
import OAI.Hierarchy.DescentEarnedPostRowLimits
import OAI.Hierarchy.DescentFixedISATariff
import OAI.Hierarchy.DescentOriginalStageFeeAxes
import OAI.Hierarchy.DescentNamedSeedCompleteInvoice
import OAI.Hierarchy.DescentNamedWideFoldTariff
import OAI.Hierarchy.DescentNamedEarnedAppendixPrice
import OAI.Hierarchy.DescentMountedPostAt

namespace OAI
/-! # One purchase threshold for every physical portion of the original finite host -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentResetGates DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentPrimitivePalette DescentTerminalCompiledPrefix.AddressPlan DescentDatedSeedStartup Filter
open DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst
noncomputable section
set_option quotPrecheck false
variable {F:Type} [Field F] (G:PoweredGadget F) (op:RotorSpec) (t f g reset n depth C drift limit ratio:ℕ)
local notation "a_" => localSocketRate G t g
local notation "κ_" => groupRate G t f g reset
local notation "u_" => Nat.clog 2 G.b*(t+1)
local notation "v_" => 2*((2+hostRate t reset*(t+1)+((t+1)*(hostRate t reset+capRate G t g+1)+11)+(0+1)+1)+5+a_)
local notation "σ_" => 1+operandExponent G (stageNumbers G t 0 f g reset 0 0)+κ_+4
local notation "χ_" => PreflightCalendar.scanExponent G t f g reset
local notation "price_" τ:arg => max (ratio+1)
  (max (NativeBranch.clockRate G t f g reset τ) (NativeBranch.privateMaskArenaRate G t f g reset τ 0))

/-- The dimensions in the following fees belong to the physical reentry and terminal shell. -/
def originalChipFactor (τ:ℕ) := price_ τ
def originalFrontierRate (n depth C t f g:ℕ) : ℕ :=
  ⌈258*reentryRate depth C+reentryExteriorRate depth C 256 (GroupStage.depthBound (atRound t) n f g)⌉₊
def originalRowCoefficient (factor rate:ℕ) := 6*(32*factor)*(3+4*rate)+2*factor
def originalAppendixPrice (factor rate:ℕ) := 10*originalRowCoefficient factor rate+102*factor
def originalChipPrice (factor rate:ℕ) :=
  let rows:=originalRowCoefficient factor rate
  22491*factor+115*(130*factor+344*rows)+24*factor+131072*(factor+32*factor+rows)+8*rows+32*factor
def originalPostPrice (factor rate:ℕ) :=
  let rows:=originalRowCoefficient factor rate
  524288*(factor+1)+7*16384*(2*factor)+(128000+262144)*factor+7*24200200*(2*factor+6*rows)+1
def originalHostPrice (τ:ℕ) :=
  let factor:=originalChipFactor G t f g reset ratio τ
  let rate:=originalFrontierRate n depth C t f g
  let a:=originalAppendixPrice factor rate
  let source:=5+a+(1135*(ratio+1)+a)
  let isa:=257*(1000*(2*(7*(ratio+6))+2)*(2*4^7+1))+256*DescentCompiler.fixedISAPrice*(ratio+6)
  earnedHostPrice source source (6+originalPostPrice factor rate+2048+originalChipPrice factor rate) ratio isa

structure OriginalPurchaseAt (τ B h:ℕ) : Prop where
  axes : ∀M,2^h≤ M→ StageFeeAxes G op drift t f g reset τ B h M
  initial : OriginalInitialPriceAt G t f g reset τ B ratio h
  verdict : WideFoldTariffAt G t f g reset τ B a_ h
  seed : CompleteAfterAt G op t f g reset drift limit (quota t) τ B (ratio+1) h
  replay : Branch.MountedCountedPostAt G op t f g reset τ B drift h
  scalar : PreflightCalendar.Ready G op t f g reset τ B drift h
  before : 2*(6*PreflightCalendar.fieldExponent G t f g reset τ+11)≤ B
  rows : PostRowsAt G t f g reset τ B n depth C drift (price_ τ) h
  chip : EarnedShellChipAt G t f g reset τ B n depth C op drift (price_ τ) h
  appendix : EarnedShellAppendixAt G t f g reset τ B n depth C op drift (price_ τ) h

/-- The bounds apply at a common height to every size and every original input. The
tail and its denominator can both be increased after the fixed word multiplier is chosen. -/
theorem original_purchase (branch:G.b≤2^(capRate G t g)) (bus:2≤ ratio) :
    ∃τ₀:ℕ,∃B₀:ℕ→ℕ,∀τ B,τ₀≤τ→ B₀ τ≤ B→
      ∀ᶠ h:ℕ in atTop,OriginalPurchaseAt G op t f g reset n depth C drift limit ratio τ B h :=by
  obtain ⟨seedTail,seedBound,buySeed⟩:=complete_after_invoice G op t f g reset drift limit (quota t)
  let τ₀:=seedTail+2*a_+(a_+8)+(5+(hostRate t reset*(t+1)+1)+(a_+u_))+
    (a_+(κ_+10))+(a_+max χ_ σ_)
  let B₀:=fun τ=>seedBound τ+20+(2*(a_+(τ+κ_+4))+u_)+v_+
    2*((τ+κ_+4)+(a_+u_)+2)+(2*((a_+u_)+(τ+κ_+4))+1)+
    2*(τ+κ_+(6*(terminalDegree G t f g reset+1)+19))+2*bookRate G t f g reset τ+
    2*(6*PreflightCalendar.fieldExponent G t f g reset τ+11)
  refine ⟨τ₀,B₀,?_⟩
  intro τ B age den
  dsimp only [τ₀] at age
  dsimp only [B₀] at den
  have large:20≤ B:=by omega
  have reserve:2*a_≤τ:=by omega
  have pack:2*(a_+(τ+κ_+4))+u_≤ B:=by omega
  have router:2*((τ+κ_+4)+(a_+u_)+2)≤ B:=by omega
  have tailMask:5+(hostRate t reset*(t+1)+1)+(a_+u_)≤τ:=by omega
  have radix:a_+(κ_+10)≤τ:=by omega
  have box:2*((a_+u_)+(τ+κ_+4))+1≤ B:=by omega
  have chart:2*(τ+κ_+(6*(terminalDegree G t f g reset+1)+19))≤ B:=by omega
  have books:2*bookRate G t f g reset τ≤ B:=by omega
  have short:2*(6*PreflightCalendar.fieldExponent G t f g reset τ+11)≤ B:=by omega
  have cpu:=Nat.le_max_right (ratio+1)
    (max (NativeBranch.clockRate G t f g reset τ) (NativeBranch.privateMaskArenaRate G t f g reset τ 0))
  filter_upwards [original_stage_fee_axes G op drift t f g reset τ B branch large reserve pack router chart,
    original_initial_price_at G t f g reset τ B ratio large reserve pack (by omega) (by omega) bus,
    all_wide_fold_tariff G t f g reset τ B a_ (by omega) (by omega) (by omega),
    buySeed τ B (ratio+1) (by omega) (by omega),
    Branch.mounted_counted_post_at G op t f g reset τ B drift large reserve (by omega) pack branch chart,
    PreflightCalendar.attained G op t f g reset τ B drift (by omega) branch short,
    earned_post_row_limits G t f g reset τ B n depth C op drift (price_ τ)
      branch large reserve pack tailMask radix box chart cpu,
    earned_shell_chip_price G t f g reset τ B n depth C op drift (price_ τ)
      branch large reserve pack router tailMask radix box chart books cpu,
    earned_shell_appendix_at G t f g reset τ B n depth C op drift (price_ τ)
      branch large reserve pack router tailMask radix box chart cpu] with h axes original vote init post ready rows chip appendix
  exact ⟨axes,original,vote,init,post,ready,short,rows,chip,appendix⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
