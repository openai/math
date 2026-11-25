import OAI.Hierarchy.DescentTerminalCalibratedShape
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # The exact public dimensions of the paid original host -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler TerminalScale Catalyst DescentTerminalCompiledPrefix DescentTerminalGraphVolume
noncomputable section
set_option quotPrecheck false

/-- The masked counter takes its dimensions from the measured format and channel table.
The remaining fields acquire their values when the public row plane is installed. -/
def shellAnchor : Shape :=
  ⟨0,0,0,1,by decide,⟨⟨0,0,0,0,0,0,0⟩,0,0,0⟩⟩

section Geometry
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F)
    (t J f g restart M τ height n d C : ℕ) (positive : 0<M)
local notation "tb" => tail τ J
local notation "S" => stageNumbers G t J f g restart M tb
local notation "k" => groupBits t J (S).hostGain (S).capGain (cutRate t f g)
local notation "W" => NativeBranch.binLimit («k»:=k) S
local notation "j" => Nat.clog 2 (NativeBranch.localLimit G S)
local notation "q" => 2^j*(G.b^(t*J)*G.b)
local notation "piece" => height/(16*(q*W))
local notation "p" => W*piece
local notation "s" => (S).firstWidth G.b p
local notation "rest" => (S).groupWidth k tb 0+k-2*j
local notation "E" => Fintype.card (Port P X.width)
local notation "H" => (S).hostSize (S).length
local notation "raw" => terminalRawRows X G S p q n d C f g
local notation "hdr" => terminalPool X G S p q W n d C f g
local notation "K" => calibratedBins X G t J f g restart M τ height n d C

def shellTemplate : Shape :=
  calibrated_shell X G t J f g restart M τ height n d C shellAnchor hdr positive

local notation "tmpl" => shellTemplate X G t J f g restart M τ height n d C positive
local notation "nativeCfg" => Branch.exteriorShape tmpl E j rest s raw hdr H
  (calibrated_hosts_positive G t J f g restart M τ positive)

theorem original_shell_eq : nativeCfg=tmpl :=rfl

theorem original_shell_fields :
    hdr≤(nativeCfg).terminal.pool ∧ raw≤(nativeCfg).terminal.plane.rawRows ∧
    (nativeCfg).terminal.pool≤hdr ∧ 0<hdr ∧ (nativeCfg).terminal.rows=K*W ∧
    (nativeCfg).terminal.pool=K*W ∧ (nativeCfg).terminal.leaves=(nativeCfg).terminal.pool ∧
    (nativeCfg).terminal.pool≤DescentDyadicSpan.span (nativeCfg).terminal.rows ∧
    (nativeCfg).terminal.plane.headerRows=hdr ∧ (nativeCfg).terminal.plane.publicRows=E*2^(j+rest) :=by
  have widthPos : 0<W:=by unfold NativeBranch.binLimit;omega
  have binsPos : 0<K:=by
    change 0<rowBudget p q W (terminalWireBudget X G S p n d C f g) ((S).copies*s*E) H 3/W
    exact Nat.div_pos (by unfold rowBudget;omega) widthPos
  exact ⟨le_rfl,le_rfl,le_rfl,Nat.mul_pos binsPos widthPos,rfl,rfl,rfl,
    DescentDyadicSpan.span_ge _,rfl,rfl⟩

end Geometry
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
