import OAI.Hierarchy.DescentTerminalBookRowCount
import OAI.Hierarchy.DescentTerminalLookupPages
import OAI.Hierarchy.DescentTerminalBinPackCheap

namespace OAI
/-! # The genuine fixed count, remainder and next-boundary tables at preflight entry -/
namespace Hierarchy.DescentTerminalControlROMs
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentTerminalLocalPortBook DescentTerminalPrimitiveArena
open scoped Fin.CommRing
noncomputable section

structure Page where
  groups : ℕ
  vertices : ℕ
  maximum : ℕ
  arity : ℕ
  tokenBits : ℕ
  q : ℕ
  binWidth : ℕ
  rows : ℕ
  start : ℕ

namespace Page
variable (p : Page)
def bytes := Book.Bytes p.groups p.vertices p.maximum p.arity p.tokenBits
def layout : Layout :=
  ⟨p.bytes,p.binWidth,p.rows,p.start,fun i=>
    ((Book.fromBytes i : Book p.groups p.vertices p.maximum p.arity p.tokenBits).rows p.q)⟩

abbrev total := p.layout.total
abbrev modulo := p.layout.modulo
abbrev boundaries := p.layout.boundaries
abbrev words := p.layout.words
abbrev stop := p.layout.stop
abbrev program (w : ℕ) := p.layout.program w
abbrev image {w : ℕ} (m : Memory w) := p.layout.image m

structure Reads {w : ℕ} (m : Memory w) : Prop where
  counts : ∀i:Fin p.bytes,p.total.read m (i.val:Word w)=countTable (G:=p.groups) (V:=p.vertices) (M:=p.maximum) (A:=p.arity) (a:=p.tokenBits) p.q i
  remainder : ∀i:Fin p.rows,p.modulo.read m (i.val:Word w)=((i.val%p.binWidth:ℕ):Word w)
  nextRow : ∀i:Fin (p.rows+1),m (p.boundaries+i.val)=(DescentTerminalBinPackCheap.boundaries w p.binWidth p.rows)[i.val]

theorem reads_iff {w : ℕ} (m : Memory w) : p.Reads m ↔ p.layout.Reads m := by
  constructor
  · intro h
    refine ⟨h.counts,h.remainder,?_⟩
    intro i
    simpa only [Page.boundaries,Page.layout,DescentTerminalBinPackCheap.boundaries,Vector.getElem_ofFn,
      DescentTerminalBinPackCheap.nextBoundary] using h.nextRow i
  · intro h
    refine ⟨h.counts,h.remainder,?_⟩
    intro i
    simpa only [Page.boundaries,Page.layout,DescentTerminalBinPackCheap.boundaries,Vector.getElem_ofFn,
      DescentTerminalBinPackCheap.nextBoundary] using h.nextRow i

theorem ranges :
    p.total.base+p.total.size≤p.stop ∧ p.modulo.base+p.modulo.size≤p.stop ∧
    p.boundaries+(p.rows+1)≤p.stop := p.layout.ranges

theorem install {w : ℕ} (m : Memory w) (room : p.stop<2^w) :
    (p.program w).Exec m (p.image m) (4+10*p.words) ∧ CheapCode (p.program w) ∧
      p.Reads (p.image m) ∧ ∀a,a<p.start ∨ p.stop≤a→p.image m a=m a := by
  obtain ⟨machine,cheap,data,unchanged⟩:=p.layout.install m room
  exact ⟨machine,cheap,(p.reads_iff _).2 data,unchanged⟩

theorem words_le : p.words≤2*p.bytes+3*p.rows+3 := p.layout.words_le

theorem tariff (w : ℕ) :
    DescentStaticWordColumn.names (p.program w)+(4+10*p.words)=25*p.words+19 :=
  p.layout.tariff w

theorem cost_le (w h : ℕ) (small : p.bytes≤2^(h/2)) :
    (DescentStaticWordColumn.names (p.program w)+(4+10*p.words))*(w+1)≤
      100*(2^(h/2)+p.rows+1)*(w+1) := p.layout.cost_le w h small

theorem transfer {w : ℕ} {m m' : Memory w} (auth : p.Reads m)
    (retained : ∀j,p.start≤j→j<p.stop→m' j=m j) : p.Reads m' :=
  (p.reads_iff _).2 (p.layout.transfer ((p.reads_iff _).1 auth) retained)

end Page
end
end Hierarchy.DescentTerminalControlROMs

end OAI
