import OAI.Hierarchy.DescentTerminalRouteInstalled
import OAI.Hierarchy.DescentTerminalPositionedBooks

namespace OAI
/-! # Native route reads from the paid six-column book and installed finite tables -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalVertexFields DescentTerminalEmitter.Compact
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {blocks v B bw:ℕ} (V:Home.Format) (S:Shape) (J:Input) (R:MaskAllocation.Channels blocks)
variable (start header q t H N A p verts W:ℕ) (qp:0<q)
variable (short:v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
variable (T:RouteSources.Tables) (prior:Fin 43→ℕ→ℕ)
local notation "ba" => afterMeter V S R start
local notation "baseArena" => rowArena S J ba
local notation "bookCols" => T.columns baseArena J.sources
local notation "c" => ScalarLiterals.columns q t H N A p verts W B S.terminal.pool bookCols
local notation "I" => ({J with sources:=c}:Input)
local notation "fixed" => ScalarLiterals.data q t H N A p verts W B S.terminal.pool qp bookCols (T.value prior)
local notation "O" => registers V S R start header
local notation "C" => meter V R start
local notation "L" => layout S I ba O
local notation "loaded" => input V S I R start header short fixed
local notation "planStart" => fun m:Memory bw=>(baseArena).mount (loaded m)
local notation "position" => fun m:Memory bw=>Suffix.positioned S L (planStart m)
local notation "μ" => fun m:Memory bw=>Suffix.events S L (C).layout (planStart m)
local notation "formatted" => fun m:Memory bw=>DescentTerminalEmitter.formatted S.terminal (L).emit (μ m)
local notation "named" => fun m:Memory bw=>DescentTerminalEmitter.named S.terminal (L).emit (μ m)
local notation "sources" => inputs S I ba

open DescentTerminalLocalPortBook DescentTerminalRecipeRows DescentTerminalBinPack DescentTerminalSpanBook
local notation "gatherBank" => (L).emit.book
local notation "RO" => (L).emit.route
local notation "outRows" => S.terminal.rows

theorem placed_route_columns (m:Memory bw) (early:Earlier S I ba (C).layout bw)
    (room:last V S I R start<2^bw)
    (sites:Fin S.sites→Site) (f:∀i,DescentTerminalLocalPortBook.Room (sites i) T.groups T.vertices T.maximum T.arity)
    (labels:∀i,(sites i).Name ↪ Word T.tokenBits) (refs:∀i,(sites i).Arg→Word T.tokenBits)
    (wp:0<T.width) (perSite:∀i,(sites i).rows T.lanes≤T.width) (rowsEq:S.terminal.rows=T.extent)
    (paid:purchased T.width (counts (q:=T.lanes) sites)≤outRows) (counter:outRows+T.width<2^bw)
    (boundaryRoom:J.boundaries+(outRows+1)≤ba)
    (issued:Book.Issued J.parts (fun i=>issue (sites i) (f i) (labels i) (refs i)) (loaded m))
    (countsROM:∀j:Fin T.bytes,J.totals.read (loaded m) (j.val:Word bw)=countTable T.lanes j)
    (boundaryROM:∀j:Fin (outRows+1),(loaded m) (J.boundaries+j.val)=
      (DescentTerminalBinPackCheap.boundaries bw T.width outRows)[j.val])
    (moduloROM:∀i:Fin outRows,J.modulo.read (loaded m) (i.val:Word bw)=((i.val%T.width:ℕ):Word bw)) :
    DescentTerminalRouteIssue.Reads RO (rows (q:=T.lanes) (K₀:=T.bins) sites wp f labels refs) (named m) := by
  let g:=gatherBank
  have equal:g=(baseArena).gather (sources 29) (sources 30) (sources 31) g.names:=rfl
  have stamps:=installed_route_tables V S J R start header q t H N A p verts W qp short T prior m early room
  have atPos:=T.books baseArena J.sources prior sources (position m) stamps.1 g rfl rfl rfl
  have atFormat:=T.books baseArena J.sources prior sources (formatted m) stamps.2.1 g rfl rfl rfl
  have limits:=stages S I ba
  have arenaRoom:(baseArena).finish<2^bw := (limits.1.trans (limits.2.1.trans
    (limits.2.2.1.trans (limits.2.2.2.1.trans limits.2.2.2.2)))).trans_lt room
  have receipts:=(baseArena).positioned_books (loaded m) early.old arenaRoom sites f labels refs wp perSite rowsEq
    paid counter boundaryRoom issued countsROM boundaryROM moduloROM (sources 29) (sources 30) (sources 31) g.names
    (equal ▸ atPos)
  have old:g.Inputs (fun i=>issue (sites i) (f i) (labels i) (refs i)) (localOwner sites wp)
      (fixedSpan (K₀:=T.bins) sites wp perSite) T.lanes (position m):=equal.symm ▸ receipts
  have valid:=(suffix_room S I ba (C).layout O early room).issuer
  have keep (b:Bank) (end_:b.base+b.size≤(baseArena).atBand 14) (u:Word bw) :
      b.read (formatted m) u=b.read (position m) u := by
    let whereAt:=b.base+u.val%b.size
    have small:whereAt<(baseArena).atBand 14:=(Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le end_
    have below:=small.trans_le (((baseArena).band_mono (by decide : 14≤22)).trans (limits.1.trans limits.2.1))
    exact (formatted_preserves S I ba O (μ m) valid below).trans
      (events_before_sort S I ba (C).layout O (planStart m) early room small)
  have active:=keep g.occupied ((baseArena).band_after (by decide : 10<14))
  have site:=keep g.site ((baseArena).band_after (by decide : 11<14))
  have local_:=keep g.localRow ((baseArena).band_after (by decide : 12<14))
  have home:=keep g.homeOffset ((baseArena).band_after (by decide : 13<14))
  have head:=keep g.head ((baseArena).band_after (by decide : 2<14))
  have measured:g.Inputs (fun i=>issue (sites i) (f i) (labels i) (refs i)) (localOwner sites wp)
      (fixedSpan (K₀:=T.bins) sites wp perSite) T.lanes (formatted m) :=
    ⟨fun i=>(active _).trans (old.occupied i),
     fun i v r used=>⟨(site _).trans (old.whereAt i v r used).1,(local_ _).trans (old.whereAt i v r used).2⟩,
     fun i=>(home _).trans (old.home i),fun i=>(head _).trans (old.book i),atFormat.low,atFormat.high,atFormat.table⟩
  have pos:0<bw:=by by_contra! z;have:=wp;rw [Nat.eq_zero_of_le_zero z] at counter;simp at counter;omega
  have bins:T.extent<2^bw:=rowsEq ▸ (by omega : outRows<2^bw)
  have size_:T.extent≤g.names.size:=by
    rw [←rowsEq]
    change outRows≤DescentTerminalEmitter.Allocation.slab S.terminal (I).indexEvents (I).formatEvents
    have:=DescentTerminalEmitter.Allocation.reserve_fit S.terminal (I).indexEvents (I).formatEvents
    unfold DescentTerminalEmitter.Allocation.reserve at this
    omega
  apply T.routes baseArena J.sources prior sources (named m) stamps.2.2 RO _ ⟨rfl,rfl,rfl,rfl,rfl⟩
  intro i
  have issuedNames:=names_read (K₀:=T.bins) sites wp f perSite labels refs g (formatted m) pos measured i
  change g.output outRows (formatted m) (g.names.base+(i.val:Word bw).val%g.names.size)=_
  rw [rowsEq,Fin.val_cast_of_lt (i.isLt.trans bins),Nat.mod_eq_of_lt (i.isLt.trans_le size_)]
  exact issuedNames

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
