import OAI.Hierarchy.DescentFixedHostShell
import OAI.Hierarchy.DescentFixedHostFallback
import OAI.Hierarchy.DescentNamedEarnedCalendarRates
import OAI.Hierarchy.DescentTerminalFundedPreflight

namespace OAI
/-! # Identification of the original funded terminal with the purchased shell and its literal input -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler TerminalScale Catalyst DescentInitialHost DescentTerminalPreflightSpace
open DescentTerminalCompiledPrefix DescentTerminalCompiledPrefix.AddressPlan DescentTerminalLocalPortBook ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 1000000

variable {F : Type} [Field F] (G : PoweredGadget F) (t f g restart τ β n d C : ℕ)
    (op : RotorSpec) (drift : ℕ) {height : ℕ} (x : ShellSource F height)
local notation "J" => Nat.log 2 height/(2*β)
local notation "tb" => tail τ J
local notation "S" => stageNumbers G t J f g restart x.sites tb
local notation "k" => groupBits t J (S).hostGain (S).capGain (cutRate t f g)
local notation "W" => NativeBranch.binLimit («k»:=k) S
local notation "j" => Nat.clog 2 (NativeBranch.localLimit G S)
local notation "q" => 2^j*(G.b^(t*J)*G.b)
local notation "piece" => height/(16*(q*W))
local notation "p" => W*piece
local notation "s" => (S).firstWidth G.b p
local notation "rest" => (S).groupWidth k tb 0+k-2*j
local notation "E" => Fintype.card (Port x.ports x.X.width)
local notation "H" => (S).hostSize (S).length
local notation "V" => earnedFormat G op S q p drift
local notation "slots" => (S).groupCount (S).length*2^k
local notation "A" => NativeBranch.localLimit G S
local notation "raw" => terminalRawRows x.X G S p q n d C f g
local notation "hdr" => terminalPool x.X G S p q W n d C f g
local notation "K" => calibratedBins x.X G t J f g restart x.sites τ height n d C
local notation "fmt" => Branch.geometryFormat G S k g p tb q drift op hdr hdr
local notation "prepared" => Branch.preflightSpec x.X G S k g p tb ({fmt with binSize:=W}:Branch.PreflightFormat)
local notation "codes" => DescentTerminalScalarHeader.range q (V).roles (V).privateWords (V).nodes (V).addresses p slots
local notation "T" => RouteSources.Tables.mk 4 slots (slots*A) A (Book.tokenBits (slots*A)) W q K

variable (front scan : ℕ) (peer homes : Bank) (wings : Fin (prepared).scalar.blocks → Fin (2*(prepared).cap) → Bank)
local notation "pages" => (prepared).scanPages scan q
local notation "rom" => front+DescentTerminalChipBootWords.total K W q piece codes
local notation "positive" => (show 0<x.sites from by have h:=x.opened;omega)

def originalPlacement : TerminalPlacement :=
  ⟨prepared,shellAnchor,fixedFallback,(pages).stop,rom,codes,front,peer,wings,
    (pages).total,(pages).modulo,homes,(pages).boundaries⟩

local notation "L" => originalPlacement G t f g restart τ β n d C op drift x front scan peer homes wings
local notation "tmpl" => shellTemplate x.X G t J f g restart x.sites τ height n d C positive
local notation "exactCfg" => Branch.exteriorShape tmpl E j rest s raw hdr H
  (calibrated_hosts_positive G t J f g restart x.sites τ positive)

theorem original_placement_shape :
    exactCfg=earnedShell G t f g restart τ β n d C x L :=rfl

theorem original_placement_input :
    (prepared).reachedInput (pages).stop rom q piece W K codes front peer wings
        (pages).total (pages).modulo homes (pages).boundaries exactCfg V fixedFallback T
        (prepared).vertices (prepared).pageBits =
      earnedInput G t f g restart τ β n d C op drift x L :=rfl

theorem original_placement_pool :
    (earnedShell G t f g restart τ β n d C x L).terminal.pool=K*W ∧
    (earnedShell G t f g restart τ β n d C x L).terminal.plane.rawRows=raw :=⟨rfl,rfl⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
