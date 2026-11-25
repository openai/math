import OAI.Hierarchy.DescentTerminalPlacedHistogram

namespace OAI
/-! # Place a source-indexed exterior shelf at the emitter's physically bought address -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalVertexFields DescentExteriorShelf DescentExterior DescentGL
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {blocks v B bw e : ℕ} (V : Home.Format) (S : Shape) (I : Input) (R : MaskAllocation.Channels blocks)
variable (start header : ℕ) (short : v*DescentTerminalVertexFields.span V.publicArity V.roles V.privateWords
    V.nodes V.addresses V.piece ≤ B) (literal : DescentTerminalEmitter.Compact.Literals I.sources)
local notation "b_" => afterMeter V S R start
local notation "orig" => takeOff S I b_
local notation "headBits_" => S.terminal.plane.headBits
local notation "restBits_" => S.terminal.plane.restBits
local notation "bitLanes_" => S.terminal.plane.bitLanes
local notation "last_" => output V S I R start header short literal

theorem history_flags_count {K T : Type} (m : Memory bw) (edges : S.terminal.plane.exteriors=e)
    (early : Earlier S I b_ (meter V R start).layout bw) (space : last V S I R start < 2^bw)
    (positive : 0 < bw) (bits : 2^headBits_*bitLanes_ ≤ bw) (seed : ℕ) (low : seed < start)
    (x : Fin e→Plane headBits_ restBits_→Fin bitLanes_→Bool) (mix : T→Fin e→DescentGL.Layout (headBits_+(headBits_+restBits_)))
    (decode : (K→Bool)→Option T) (z : K⊕Hidden e headBits_ restBits_ bitLanes_→Bool)
    (good : m seed=0 ↔ ∃c,decode (z∘Sum.inl)=some c)
    (printed : ∀c,decode (z∘Sum.inl)=some c→Loaded orig (mix c) x (z∘Sum.inr) m) :
    (last_ m seed=0 ∧ last_ m (flagAt (j:=headBits_) (r:=restBits_) (t:=bitLanes_) (e:=e) orig)=0) ↔
      ∃c,proposed decode mix x z=some c := by
  subst e
  exact history_flags V S I R start header short literal m early space positive bits seed low x mix decode z good printed

/-- Every immutable original input word lies below the first terminal allocation. -/
theorem output_before (m : Memory bw)
    (early : Earlier S I b_ (meter V R start).layout bw) (space : last V S I R start < 2^bw)
    {a : ℕ} (ha : a < start) : last_ m a=m a := by
  exact original V S I R start header short literal m early space ha


end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
