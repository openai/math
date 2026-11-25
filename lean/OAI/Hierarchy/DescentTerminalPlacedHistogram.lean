import OAI.Hierarchy.DescentTerminalPlacedMass

namespace OAI
/-! # Admission from the original incoming history at its two physical address bands -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalVertexFields DescentTerminalRowArena DescentExteriorShelf DescentExterior DescentGL
open DescentTerminalDenseHeaderRAM DescentTerminalHeaderGroups DescentTerminalCableOrder Computability.BorderVNP.Crossing
open scoped BigOperators
noncomputable section
variable {blocks v B bw:ℕ} (V:Home.Format) (S:Shape) (I:Input) (R:MaskAllocation.Channels blocks)
variable (start header:ℕ) (short:v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
variable (literal:DescentTerminalEmitter.Compact.Literals I.sources)
local notation "C" => meter V R start
local notation "O" => registers V S R start header
local notation "b_" => afterMeter V S R start
local notation "orig" => takeOff S I b_
local notation "P" => S.terminal.plane
local notation "loaded" => input V S I R start header short literal
local notation "end_" => output V S I R start header short literal


theorem before_print (m : Memory bw) (early:Earlier S I b_ (C).layout bw) (space:last V S I R start<2^bw)
    {x:ℕ} (small:x<b_) : end_ m x=loaded m x := by
  let A:=rowArena S I b_
  let L:=layout S I b_ O
  let μ:=Suffix.events S L (C).layout (A.mount (loaded m))
  have room:=suffix_room S I b_ (C).layout O early space
  obtain ⟨s0,s1,s2,s3,s4⟩:=stages S I b_
  have high:x<orig:=small.trans_le ((A.start_le 22).trans (s0.trans s1))
  have lo:=before S I b_ O x (by change x<b_+2;omega)
  have first_:DescentTerminalEmitter.BeforeKey S.terminal L.emit x:=by
    constructor <;> change x<orig+_ <;> omega
  have last_:=after_start S I b_ O (a:=x) (by change x<orig+_;omega)
  exact (DescentTerminalEmitter.printed_before S.terminal L.emit μ room.issuer first_ last_).trans
    ((Suffix.early S L (C).layout (A.mount (loaded m)) room lo.original lo.slot lo.page).trans
      (A.mount_before _ small))

theorem original (m:Memory bw) (early:Earlier S I b_ (C).layout bw) (space:last V S I R start<2^bw)
    {x:ℕ} (low:x<start) : end_ m x=m x := by
  have bound:start≤b_:=by change start≤ start+_+_+_+_+3;omega
  exact (before_print V S I R start header short literal m early space (low.trans_le bound)).trans
    (input_frame V S I R start header short literal m (.inl low))

variable {geo H q p:ℕ} {Pin:Type} [Fintype Pin] {bits:Pin→ℕ}
theorem histogram (m:Memory bw) (early:Earlier S I b_ (C).layout bw) (space:last V S I R start<2^bw)
    (N:Network geo Pin bits) (home:N.Site→Fin H) (native:N.Edge↪Fin (Fintype.card N.Edge))
    (ex:Pin↪ℕ) (node:N.Site↪ℕ) (ops:∀v,DescentKernelHistory.Boundary N v↪ℕ)
    (hq:0<q) (hp:0<p) (bound:ℕ) (all:∀e,pairIndex N home e<bound)
    (count:0<(P).headerRows) (rows:(stream N home native ex node ops q hp bound).length≤(P).headerRows)
    (prior:∀i,(I.cable i).base+(I.cable i).size≤ start)
    (inputs:Reads (bodyPlane S I b_).header (padded (n:=(P).headerRows) (stream N home native ex node ops q hp bound)) m)
    (whole:(∑e,N.width e)/(q*p)<2^bw) (tail_:(∑e,N.width e)%(q*p)<2^bw) :
    (end_ m (wholeAddress S (layout S I b_ O))).val=(∑e,N.width e)/(q*p) ∧
      (end_ m (tailAddress S (layout S I b_ O))).val=(∑e,N.width e)%(q*p) := by
  have bound_:start≤b_:=by change start≤ start+_+_+_+_+3;omega
  have prev (i:Fin 5) (a:Word bw) : (I.cable i).read (loaded m) a=(I.cable i).read m a:=by
    unfold Bank.read
    exact input_frame V S I R start header short literal m (.inl
      ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le (prior i)))
  apply mass S I b_ (C).layout O (loaded m) early space N home native ex node ops hq hp bound all count rows
    (fun i=>(prior i).trans bound_) _ whole tail_
  obtain ⟨widths,offset,next,carry,format⟩:=inputs
  exact ⟨fun i=>(prev 0 _).trans (widths i),fun i=>(prev 1 _).trans (offset i),
    fun a r=>(prev 2 _).trans (next a r),fun a r=>(prev 3 _).trans (carry a r),
    fun a r=>(prev 4 _).trans (format a r)⟩

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
