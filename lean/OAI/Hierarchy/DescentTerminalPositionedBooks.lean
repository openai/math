import OAI.Hierarchy.DescentTerminalRouteSources
import OAI.Hierarchy.DescentTerminalSiteCursorPlan
import OAI.Hierarchy.DescentTerminalReachedBooks

namespace OAI
/-! # The five live gather sources at the end of the row and offset passes -/
namespace Hierarchy.DescentTerminalRowArena.Arena
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalLocalPortBook DescentTerminalRecipeRows
open DescentTerminalRowPlan DescentTerminalBinPack DescentTerminalSpanBook
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable (A:Arena) {w G V M D a W q cap:ℕ}

def gather (lo hi menu names:Bank) : Gather :=
  ⟨A.row.locate.active,A.row.locate.owner,A.row.books,A.row.locate.localRow,A.offset.offsets,lo,hi,menu,names⟩

theorem gather_routes (lo hi menu names:Bank) :
    Routes A.row A.offset (A.gather lo hi menu names) A.sites A.rows := by
  have stride:=A.stride_min
  have less (b j:ℕ) (order:b<j) (i:Fin A.sites) : A.atBand b+i.val<A.atBand j :=
    (Nat.add_lt_add_left (show i.val<A.stride by omega) _).trans_le (A.band_after order)
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,(by change A.sites≤A.stride;omega),?_,?_,?_⟩
  · intro i
    exact ⟨less 2 9 (by decide) i,less 2 7 (by decide) i,less 2 6 (by decide) i,
      less 2 5 (by decide) i,less 2 4 (by decide) i,less 2 3 (by decide) i⟩
  · intro i
    exact ⟨less 5 7 (by decide) i,less 5 9 (by decide) i⟩
  · rintro b (rfl|rfl|rfl|rfl)
    exact A.band_after (by decide : 10<13)
    exact A.band_after (by decide : 11<13)
    exact A.band_after (by decide : 12<13)
    exact A.band_after (by decide : 2<13)

theorem plan_before (m:Memory w) (low:A.Lower w) (fit:A.finish<2^w) {x:ℕ} (below:x<A.start) :
    result A.row A.sites A.rows (A.mount m) x=m x := by
  have before (j) := below.trans_le (A.start_le j)
  exact (before_publishing _ _ (A.row_room low fit)
    ⟨before 9,before 7,before 6,before 5,before 4,before 3⟩ (before 2)).trans (A.mount_before m below)

theorem positioned_books (m:Memory w) (low:A.Lower w) (fit:A.finish<2^w)
    (sites:Fin A.sites→Site) (f:∀i,DescentTerminalLocalPortBook.Room (sites i) G V M D)
    (labels:∀i,(sites i).Name ↪ Word a) (refs:∀i,(sites i).Arg→Word a)
    (wp:0<W) (perSite:∀i,(sites i).rows q≤W) (rowsEq:A.rows=cap*W)
    (paid:purchased W (counts (q:=q) sites)≤A.rows) (counter:A.rows+W<2^w)
    (boundaryRoom:A.boundaries+(A.rows+1)≤A.start)
    (issued:Book.Issued A.parts (fun i=>issue (sites i) (f i) (labels i) (refs i)) m)
    (countsROM:∀j:Fin (Book.Bytes G V M D a),A.countTable.read m (j.val:Word w)=DescentTerminalLocalPortBook.countTable q j)
    (boundaryROM:∀j:Fin (A.rows+1),m (A.boundaries+j.val)=(DescentTerminalBinPackCheap.boundaries w W A.rows)[j.val])
    (moduloROM:∀i:Fin A.rows,A.modulo.read m (i.val:Word w)=((i.val%W:ℕ):Word w))
    (lo hi menu names:Bank)
    (rom:Fixed (G:=G) (V:=V) (M:=M) (A:=D) (a:=a) (W:=W) (q:=q) (A.gather lo hi menu names)
      (DescentTerminalSiteOffsets.result A.offset A.sites (result A.row A.sites A.rows (A.mount m)))) :
    (A.gather lo hi menu names).Inputs (fun i=>issue (sites i) (f i) (labels i) (refs i))
      (localOwner (q:=q) sites wp) (fixedSpan (q:=q) (K₀:=cap) sites wp perSite) q
      (DescentTerminalSiteOffsets.result A.offset A.sites (result A.row A.sites A.rows (A.mount m))) := by
  have stride:=A.stride_min
  have enough:A.sites≤A.stride:=by omega
  have bank:=A.fits_band fit (by decide : 6<7) (by decide)
  have links : Linked (w:=w) A.row A.sites := ⟨rfl,rfl,rfl,rfl,enough,enough,bank⟩
  have positive:0<w:=by have:=bank.1;have:=bank.2.1;by_contra! neg;simp [Nat.eq_zero_of_le_zero neg] at *;omega
  have ready:=A.row_room low fit
  have owned:=A.gather_routes lo hi menu names
  have copied:Book.Issued A.parts (fun i=>issue (sites i) (f i) (labels i) (refs i)) (A.mount m) :=
    ⟨fun i k=>(A.mounted_read m _ (low.source k) _).trans (issued.source i k),
      fun k u=>(A.mounted_read m _ (low.weights k) _).trans (issued.values k u)⟩
  have boundaries:=A.mounted_first_last m low fit sites f (fun i x=>labels i x) refs
    wp perSite paid counter boundaryRoom issued countsROM boundaryROM
  have modulo (i:Fin A.rows):A.offset.modulo.read (result A.row A.sites A.rows (A.mount m)) (i.val:Word w)=((i.val%W:ℕ):Word w) :=
    (A.plan_before m low fit ((Nat.add_lt_add_left (Nat.mod_lt _ low.modulo.1) _).trans_le low.modulo.2.2)).trans (moduloROM i)
  rw [rowsEq] at ready owned paid rom modulo ⊢
  apply book_inputs A.row A.offset (A.gather lo hi menu names) sites f labels refs wp perSite (A.mount m)
    ready links owned enough positive paid (enough.trans_lt bank.2.1) (by omega)
    (by change cap*W≤A.stride;omega) copied (A.mounted_half_header fit m)
    (fun i=> (boundaries i).1) (fun i=> (boundaries i).2) modulo rom

end
end Hierarchy.DescentTerminalRowArena.Arena

end OAI
