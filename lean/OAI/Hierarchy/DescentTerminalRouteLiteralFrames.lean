import OAI.Hierarchy.DescentTerminalRouteFrames

namespace OAI
/-! # The same installed literal is visible during book positioning, gathering and route issue -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalVertexFields DescentTerminalRowArena DescentExteriorShelf DescentExterior DescentGL
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {blocks v B bw:ℕ} (V:Home.Format) (S:Shape) (I:Input) (R:MaskAllocation.Channels blocks)
variable (start header:ℕ) (short:v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
variable (literal:DescentTerminalEmitter.Compact.Literals I.sources)
local notation "C" => meter V R start
local notation "O" => registers V S R start header
local notation "b_" => afterMeter V S R start
local notation "orig" => takeOff S I b_
local notation "loaded" => input V S I R start header short literal


local notation "L" => layout S I b_ O
local notation "arena_" => rowArena S I b_
local notation "μ" => fun m:Memory bw=>Suffix.events S L (C).layout ((arena_).mount (loaded m))


local notation "src" => pageEnd S I b_
local notation "shelf" => DescentTerminalEmitter.Compact.loaded src I.sources literal
local notation "route" => fun m:Memory bw=>DescentTerminalEmitter.routed S.terminal (L).emit (μ m)

local notation "η" => fun m:Memory bw=>Suffix.positioned S L ((arena_).mount (loaded m))
private theorem read_at_address {w : ℕ} (bank : Bank) (old new : Memory w) (idx : Word w)
    (same : new (bank.base + idx.val % bank.size) = old (bank.base + idx.val % bank.size)) :
    bank.read new idx = bank.read old idx := same

theorem literal_stages (m:Memory bw) (early:Earlier S I b_ (C).layout bw) (room:last V S I R start<2^bw)
    (j:Fin 43) {n:ℕ} (bought:I.sources j=.literal n)
    (u:Fin (DescentTerminalEmitter.Compact.size (I.sources j))) :
    let bank:=DescentTerminalEmitter.Compact.view src I.sources j
    bank.read (η m) (u.val:Word bw)=(literal j u:Word bw) ∧
    bank.read (DescentTerminalEmitter.formatted S.terminal (L).emit (μ m)) (u.val:Word bw)=(literal j u:Word bw) ∧
    bank.read (DescentTerminalEmitter.named S.terminal (L).emit (μ m)) (u.val:Word bw)=(literal j u:Word bw) := by
  let bank:=DescentTerminalEmitter.Compact.view src I.sources j
  have limits:=stages S I b_
  have top:orig<2^bw:=limits.2.2.1.trans_lt (limits.2.2.2.1.trans_lt (limits.2.2.2.2.trans_lt room))
  have read:=DescentTerminalEmitter.Compact.bank_read src I.sources literal m top j bought u
  have bounds:bank.base+bank.size≤orig:=DescentTerminalEmitter.Compact.literal_end src I.sources j bought
  have startAt:src≤bank.base:=by simp [bank,DescentTerminalEmitter.Compact.view,bought]
  let a:=bank.base+(u.val:Word bw).val%bank.size
  have below:a<orig:=(Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le bounds
  have above:src≤a:=startAt.trans (Nat.le_add_right ..)
  have inputs:loaded m a=shelf m a:=by
    exact MaskAllocation.terminal_frame (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
      (A:=V.addresses) (p:=V.piece) (groups:=V.groups) (sites:=S.sites) R start header short (shelf m) a
      (.inr ((((arena_).start_le 22).trans limits.1).trans above))
  have ev:μ m a=shelf m a:=(events_after S I b_ (C).layout O (loaded m) early room above).trans inputs
  have valid:=(suffix_room S I b_ (C).layout O early room).issuer
  have stable:=limits.1.trans above
  have fit:=((limits.1.trans limits.2.1).trans_lt top)
  have ret:η m a=shelf m a :=
    ((arena_).offset_after _ stable).trans (((arena_).plan_after _ fit stable).trans
      ((mounted_high S I b_ (loaded m) stable).trans inputs))
  have transfer (memory : Memory bw) (same : memory a = shelf m a) :
      bank.read memory (u.val : Word bw) = (literal j u : Word bw) :=
    (read_at_address bank (shelf m) memory (u.val : Word bw) same).trans read
  refine ⟨transfer _ ret, transfer _ ?_, transfer _ ?_⟩
  · exact (formatted_preserves S I b_ O (μ m) valid below).trans ev
  · exact (named_preserves S I b_ O (μ m) valid below).trans ev

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
