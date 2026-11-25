import OAI.Hierarchy.DescentTerminalPreflightEarlier

namespace OAI
/-! # Fixed fallback for the paid terminal address plan -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open ProtocolRAM DescentTerminalCompiledPrefix DescentTerminalRowArena DescentTerminalVertexFields
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (x : Spec) (begin_ rom q piece W K codes front : ℕ) (peer : Bank)
    (priorCables : Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (total modulo homes : Bank) (boundary : ℕ) (cfg : Shape) (V : Home.Format)
    (T : AddressPlan.RouteSources.Tables) (vertices B : ℕ)
local notation "make_" z:arg => x.reachedInput begin_ rom q piece W K codes front peer priorCables
    total modulo homes boundary cfg V z T vertices B
local notation "fixed_" => make_ AddressPlan.fixedFallback
local notation "mask_" => x.maskBase begin_
local notation "R_" => x.channels begin_
local notation "base_" => AddressPlan.afterMeter V cfg R_ mask_

/-- Changing the fallback can change only the archived packed-counter layout.
The actual 43 column declarations and all terminal input banks are preserved. -/
theorem reachedInput_eq_fixed (other : AddressPlan.Input) :
    make_ other = { fixed_ with legacy := other.legacy } := by rfl

/-- Each attained input among the 43 emit columns ends before the first emitter
page. Literal columns use the public tables produced by the paid prefix. -/
theorem fixed_originals :
    DescentTerminalEmitter.Compact.Earlier (AddressPlan.pageEnd cfg fixed_ base_) (fixed_).sources := by
  have room : mask_≤base_ := by change mask_≤ mask_+_+_+_+_+3; omega
  exact x.priced_earlier begin_ rom q (W*piece) peer priorCables total modulo homes boundary cfg
    AddressPlan.fixedFallback T base_ V.roles V.privateWords V.nodes V.addresses (W*piece)
    vertices W B cfg.terminal.pool room

/-- The genuine paid, signed, dense-header and identity inputs discharge all the
address-plan conditions for the literal fixed choice. -/
theorem fixed_earlier {w : ℕ} (paid oldActors : Fin x.scalar.blocks→Bank)
    (boot : x.Before begin_ paid oldActors priorCables peer total modulo homes boundary)
    (romTop : rom+DescentTerminalDenseHeaderBoot.extent q (W*piece)≤x.literalBase begin_)
    (full : front+DescentTerminalPublicIdentity.total K W q piece codes cfg.terminal.plane.rawRows
      cfg.packets≤ mask_)
    (end_ : AddressPlan.last V cfg fixed_ R_ mask_ < 2^w) :
    AddressPlan.Earlier cfg fixed_ base_ (AddressPlan.meter V R_ mask_).layout w :=
  x.earlier begin_ rom q piece W K codes front peer priorCables total modulo homes boundary
    cfg V AddressPlan.fixedFallback T vertices B paid oldActors boot romTop full end_

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
