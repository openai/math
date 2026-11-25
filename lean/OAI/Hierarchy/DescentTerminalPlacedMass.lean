import OAI.Hierarchy.DescentTerminalPlacedRead
import OAI.Hierarchy.DescentTerminalMaskedMass

namespace OAI
/-! # The actual final histogram mass from five earlier cable-header columns -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalVertexFields DescentTerminalRowArena DescentTerminalEmitter DescentTerminalHeaderGroups
open DescentTerminalDenseHeaderRAM DescentTerminalCableOrder Computability.BorderVNP.Crossing
open scoped BigOperators
noncomputable section
set_option quotPrecheck false
variable {blocks w:ℕ} (S:DescentTerminalCompiledPrefix.Shape) (I:Input) (base:ℕ)
variable (F:MaskedShelf blocks) (O:DescentPrivateExponentRAM.Banks)
local notation "A" => rowArena S I base
local notation "L" => layout S I base O
local notation "E" => S.terminal
local notation "P" => (E).plane
local notation "dl" => (L).emit.plane
local notation "orig" => takeOff S I base
local notation "hd" => DescentTerminalDataPlane.Arena.headerBase P orig
local notation "ext" => publicHeader S I base
local notation "finalBase" => DescentTerminalDataPlane.Arena.finish P orig
local notation "z" => DescentTerminalDataPlane.Arena.size (P).headerRows

theorem eof_live (rem:Bool) (yes:0<(P).headerRows):
    let addr:=if rem then tailAddress S L else wholeAddress S L
    Later (L).emit addr ∧ addr<(chip S I base).first := by
  have cap:=DescentTerminalDataPlane.Arena.room (P).headerRows
  have g : hd+4*z≤finalBase:=by change _≤(hd+4*z)+4*z;omega
  have hdr:(ext).rem.base=hd+4*z:=by change (hd+4*z)+0*z=_;omega
  have first:finalBase≤(chip S I base).first:=(stages S I base).2.2.2.1
  have lw:wholeAddress S L<(ext).rem.base:=by
    rw [hdr];change hd+1*z+((P).headerRows-1)<hd+4*z;omega
  have lr:tailAddress S L<(ext).rem.base:=by
    rw [hdr];change hd+0*z+((P).headerRows-1)<hd+4*z;omega
  have end_:(ext).rem.base≤finalBase:=by rw [hdr];exact g
  cases rem
  · exact ⟨DescentTerminalEmitter.Allocation.protected E I.indexEvents I.formatEvents finalBase _ _ ext I.blank
      (lw.trans_le end_) lw,lw.trans_le (end_.trans first)⟩
  · exact ⟨DescentTerminalEmitter.Allocation.protected E I.indexEvents I.formatEvents finalBase _ _ ext I.blank
      (lr.trans_le end_) lr,lr.trans_le (end_.trans first)⟩

theorem file_low (m:Memory w) (old:Earlier S I base F w) (space:endAddress S I base<2^w)
    {x:ℕ} (low:x<base) :
    DescentTerminalDataPlane.file P dl (Suffix.events S L F ((A).mount m)) x=m x := by
  let μ:=Suffix.events S L F ((A).mount m)
  have room_:=suffix_room S I base F O old space
  have row:=before S I base O x (by change x<base+2;omega)
  have read:μ x=m x:=(Suffix.early S L F ((A).mount m) room_ row.original row.slot row.page).trans ((A).mount_before m low)
  have stages_:=stages S I base
  have high:x<orig:=low.trans_le (((A).start_le 22).trans (stages_.1.trans stages_.2.1))
  have after_:=after_start S I base O (a:=x) (by change x<orig+_;omega)
  have pre:BeforeKey E (L).emit x:=by constructor <;> change x<orig+_ <;> omega
  have end_:=printed_before E (L).emit μ room_.issuer pre after_
  rw [after_plane E (L).emit μ room_.issuer after_.later,DescentTerminalDataPlane.finalMem,
    before_inputs _ _ room_.issuer.plane.widths after_.widths] at end_
  exact end_.trans read

variable {geo H q p:ℕ} {Pin:Type} [Fintype Pin] {bits:Pin→ℕ}
theorem mass (m:Memory w) (old:Earlier S I base F w) (space:endAddress S I base<2^w)
    (N:Network geo Pin bits) (home:N.Site→Fin H) (native:N.Edge↪Fin (Fintype.card N.Edge))
    (ex:Pin↪ℕ) (node:N.Site↪ℕ) (ops:∀v,DescentKernelHistory.Boundary N v↪ℕ)
    (hq:0<q) (hp:0<p) (bound:ℕ) (all:∀e,pairIndex N home e<bound)
    (count:0<(P).headerRows) (rows:(stream N home native ex node ops q hp bound).length≤(P).headerRows)
    (prior:∀i,(I.cable i).base+(I.cable i).size≤base)
    (inputs:Reads (dl).header (padded (n:=(P).headerRows) (stream N home native ex node ops q hp bound)) m)
    (whole:(∑e,N.width e)/(q*p)<2^w) (tail_:(∑e,N.width e)%(q*p)<2^w) :
    ((tailImage S I base F O m) (wholeAddress S L)).val=(∑e,N.width e)/(q*p) ∧
      ((tailImage S I base F O m) (tailAddress S L)).val=(∑e,N.width e)%(q*p) := by
  let file_:=DescentTerminalDataPlane.file P dl (Suffix.events S L F ((A).mount m))
  have prev (i:Fin 5) (a:Word w) : (I.cable i).read file_ a=(I.cable i).read m a:=by
    unfold Bank.read
    apply file_low S I base F O m old space
    exact (Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le (prior i)
  apply suffix_mass S L F ((A).mount m) (suffix_room S I base F O old space) count
    (eof_live S I base O false count).1 (eof_live S I base O true count).1 N home native ex node ops hq hp bound all rows _ whole tail_
  obtain ⟨widths,offset,next,carry,format⟩:=inputs
  exact ⟨fun i=>(prev 0 _).trans (widths i),fun i=>(prev 1 _).trans (offset i),
    fun a r=>(prev 2 _).trans (next a r),fun a r=>(prev 3 _).trans (carry a r),
    fun a r=>(prev 4 _).trans (format a r)⟩

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
