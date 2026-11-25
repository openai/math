import OAI.Hierarchy.DescentFixedHostShellRows
import OAI.Hierarchy.DescentNamedPaidShape
import OAI.Hierarchy.DescentNamedPreflightFormat
import OAI.Hierarchy.DescentTerminalFieldSum
import OAI.Hierarchy.DescentTerminalAppendixBinMonotone
import OAI.Hierarchy.DescentTerminalPublicIdentity
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Exact chip dimensions and the two public header addresses on the original shell -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler TerminalScale Catalyst DescentInitialHost DescentTerminalCompiledPrefix
open DescentTerminalCompiledPrefix.AddressPlan
open DescentTerminalGraphVolume DescentTerminalPreflightSpace DescentTerminalVertexFields
noncomputable section
set_option quotPrecheck false

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

variable (op : RotorSpec) (drift : ℕ)
local notation "fmt" => Branch.geometryFormat G S k g p tb q drift op hdr hdr
local notation "prepared" => Branch.preflightSpec X G S k g p tb ({fmt with binSize:=W}:Branch.PreflightFormat)
local notation "V" => earnedFormat G op S q p drift

theorem original_shell_short :
    (prepared).vertices*span (V).publicArity (V).roles (V).privateWords (V).nodes (V).addresses (V).piece≤
      (prepared).pageBits :=by
  let vertices:=(prepared).vertices
  let field:=span (V).publicArity (V).roles (V).privateWords (V).nodes (V).addresses (V).piece
  change vertices*field≤ max 1 (vertices*(field+1))
  exact (Nat.mul_le_mul_left vertices (Nat.le_succ field)).trans (le_max_right ..)

end Geometry

theorem original_shell_rom (a : Spec) (census firstFree K W q piece codes edgeRows publicRows front : ℕ)
    (archived : front+DescentTerminalPublicIdentity.total K W q piece codes edgeRows publicRows≤firstFree)
    (beforeCensus : firstFree≤census) :
    (front+DescentTerminalChipBootWords.total K W q piece codes)+DescentTerminalDenseHeaderBoot.extent q (W*piece)≤
      firstFree ∧
    (front+DescentTerminalChipBootWords.total K W q piece codes)+DescentTerminalDenseHeaderBoot.extent q (W*piece)≤
      a.literalBase census ∧
    front+DescentTerminalPublicIdentity.total K W q piece codes edgeRows publicRows≤a.maskBase census :=by
  have header:=(original_rom_end K W q piece codes edgeRows publicRows front).trans archived
  have first:=a.cohort_le census
  obtain ⟨olda,oldb,oldc,oldd,olde,oldf,oldg,oldh,oldi⟩:=a.layers census
  exact ⟨header,by omega,by omega⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
