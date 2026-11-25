import OAI.Hierarchy.DescentTerminalPlacedHistogram
import OAI.Hierarchy.DescentTerminalPlacedChip
import OAI.Hierarchy.DescentTerminalBoot
import OAI.Hierarchy.DescentTerminalMaskCounter

namespace OAI
/-! # Admission from the original incoming history at its two physical address bands -/
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

private theorem read_of_same_address {w : ℕ} (bank : Bank) (old new : Memory w) (idx : Word w)
    (same : new (bank.base + idx.val % bank.size) = old (bank.base + idx.val % bank.size)) :
    bank.read new idx = bank.read old idx := same

private theorem routed_preserves_address {w addr : ℕ}
    (shape : DescentTerminalEmitter.Shape) (lay : DescentTerminalEmitter.Layout) (memory : Memory w)
    (valid : DescentTerminalEmitter.Room shape lay w)
    (early : DescentTerminalEmitter.BeforeKey shape lay addr)
    (later : DescentTerminalEmitter.AfterFlights shape lay addr) :
    DescentTerminalEmitter.routed shape lay memory addr = memory addr := by
  have h := DescentTerminalEmitter.leaf_early shape lay
    (DescentTerminalEmitter.routed shape lay memory) valid later.later.leaves later.later.scalar
  exact h.symm.trans (DescentTerminalEmitter.printed_before shape lay memory valid early later)

/-- An actual ROM installed in the compact literal header is still readable after
the width flights, sparse index updates, and route compilation. -/
theorem literal_routed (m:Memory bw) (early:Earlier S I b_ (C).layout bw) (room:last V S I R start<2^bw)
    (j:Fin 43) {n:ℕ} (bought:I.sources j=.literal n)
    (u:Fin (DescentTerminalEmitter.Compact.size (I.sources j))) :
    (DescentTerminalEmitter.Compact.view src I.sources j).read (route m) (u.val:Word bw)=(literal j u:Word bw) := by
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
  have pos:=after_start S I b_ O (a:=a) (by change a<orig+_;omega)
  have first_:DescentTerminalEmitter.BeforeKey S.terminal (L).emit a:=by constructor <;> change a<orig+_ <;> omega
  have valid:=(suffix_room S I b_ (C).layout O early room).issuer
  have kept := routed_preserves_address S.terminal (L).emit (μ m) valid first_ pos
  have value := read_of_same_address bank (shelf m) (route m) (u.val : Word bw) (kept.trans ev)
  exact value.trans read

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
