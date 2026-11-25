import OAI.Hierarchy.DescentTerminalSiteOffsets
import OAI.Hierarchy.DescentTerminalRowFrames
import OAI.Hierarchy.DescentTerminalSpanBook

namespace OAI
/-! # The actual occupied and empty row records presented to the shared port-book ROM -/
namespace Hierarchy.DescentTerminalRowPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalLocalPortBook DescentTerminalSpanBook
open DescentTerminalRecipeRows DescentTerminalBinPack
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {S cap W q w G V M A a : ℕ}
variable (L : Layout) (P : DescentTerminalSiteOffsets.Layout) (g : Gather)

structure Routes (S n : ℕ) : Prop where
  offsets : g.homeOffset=P.offsets
  book : g.head=L.books
  active : g.occupied=L.locate.active
  site : g.site=L.locate.owner
  «local» : g.localRow=L.locate.localRow
  number : P.first=L.siteFirst
  cap : S≤P.offsets.size
  books : ∀i:Fin S,Lower L (L.books.base+i.val)
  starts : ∀i:Fin S,L.siteFirst.base+i.val<L.mark.mark.base ∧ L.siteFirst.base+i.val<L.locate.number.base
  saved : ∀(b:Bank),b=g.occupied ∨ b=g.site ∨ b=g.localRow ∨ b=g.head → b.base+b.size≤P.offsets.base

local notation "n" => cap*W

variable (sites : Fin S→Site) (f : ∀i,DescentTerminalLocalPortBook.Room (sites i) G V M A)
    (names : ∀i,(sites i).Name ↪ Word a) (args : ∀i,(sites i).Arg→Word a)
    (pos:0<W) (fit : ∀i,(sites i).rows q≤W) (m : Memory w)
local notation "B" => fun i=>issue (sites i) (f i) (names i) (args i)
local notation "mem" => result L S n m
local notation "out" => DescentTerminalSiteOffsets.result P S mem

structure Fixed (g : Gather) (m : Memory w) : Prop where
  low : ∀r:Fin W,g.low.read m (r.val:Word w)=((Book.Bytes G V M A a*r.val:ℕ):Word w)
  high : ∀r:Fin W,g.high.read m (r.val:Word w)=((W*Book.Bytes G V M A a*r.val:ℕ):Word w)
  table : ∀i:Fin (W*(W*Book.Bytes G V M A a)),g.menu.read m (i.val:Word w)=
    ((Book.menu (G:=G) (V:=V) (M:=M) (A:=A) (a:=a) q i).val:Word w)

theorem book_inputs (ok : Room L S n w) (links : Linked (w:=w) L S) (route : Routes L P g S n)
    (heads:S≤L.books.size) (positive : 0<w) (paid : purchased W (counts (q:=q) sites)≤n)
    (sFit:S<2^w) (nFit:n<2^w) (localRoom:n≤L.locate.localRow.size)
    (parts : Book.Issued L.parts B m)
    (half : ∀i:Fin S,L.mark.half.read (header L S m) ((DescentTerminalHeaderScatter.field i 0).val:Word w)=(i.val:Word w))
    (starts : ∀i:Fin S,header L S m (L.siteFirst.base+i.val)=(first W (counts (q:=q) sites) i:Word w))
    (ends : ∀i:Fin S,header L S m (L.siteLast.base+i.val)=(last W (counts (q:=q) sites) i:Word w))
    (modulo : ∀i:Fin n,P.modulo.read mem (i.val:Word w)=((i.val%W:ℕ):Word w))
    (rom : Fixed (G:=G) (V:=V) (M:=M) (A:=A) (a:=a) (W:=W) (q:=q) g out) :
    g.Inputs B (localOwner (q:=q) sites pos) (fixedSpan (q:=q) (K₀:=cap) sites pos fit) q out := by
  have old (b:Bank) (pos:b=g.occupied ∨ b=g.site ∨ b=g.localRow ∨ b=g.head) (nz:0<b.size) (x:Word w) :
      b.read out x=b.read mem x:=by
    change out (b.base + x.val % b.size) = mem (b.base + x.val % b.size)
    apply DescentTerminalSiteOffsets.early P S mem
    have:=route.saved b pos
    have:=Nat.mod_lt x.val nz
    omega
  have truth (u:Fin n) := owner L sites m ok links fit positive pos paid sFit nFit localRoom half starts ends u
  have firsts (i:Fin S) : P.first.read mem (i.val:Word w)=(first W (counts (q:=q) sites) i:Word w):=by
    rw [route.number,Bank.read,Fin.val_cast_of_lt (i.isLt.trans sFit),Nat.mod_eq_of_lt (i.isLt.trans_le links.firstSize),
      after_header L m ok (route.starts i).1 (route.starts i).2,starts]
  have firstBound (v : Fin S) : first W (counts (q:=q) sites) v < n := by
    have finish : first W (counts (q:=q) sites) v + counts (q:=q) sites v ≤ n := by
      rw [←cursor_step]
      exact ((cursor_mono W (counts (q:=q) sites) (show v.val+1≤S from v.isLt)).trans
        (end_le_purchased pos (counts (q:=q) sites))).trans paid
    have live : 0 < counts (q:=q) sites v := by simp [counts,Site.rows]
    omega
  have off (i:Fin S) := DescentTerminalSiteOffsets.actual P sites q W mem firsts firstBound modulo i
  have nzActive:0<g.occupied.size:=route.active ▸ ok.locate.active.1
  have nzSite:0<g.site.size:=route.site ▸ ok.locate.owner.1
  refine ⟨?_,?_,?_,?_,rom.low,rom.high,rom.table⟩
  · intro i
    rw [old _ (Or.inl rfl) nzActive,route.active,←DescentTerminalSpanBook.«matches» sites fit pos i]
    exact (truth i).1
  · intro i v r h
    have localNz:0<g.localRow.size:=by rw [route.local];have:=i.isLt;omega
    rw [old _ (Or.inr (Or.inl rfl)) nzSite,old _ (Or.inr (Or.inr (Or.inl rfl))) localNz,route.site,route.local]
    exact (truth i).2 v r ((DescentTerminalSpanBook.«matches» sites fit pos i).trans h)
  · intro i
    rw [route.offsets,Bank.read,Fin.val_cast_of_lt (i.isLt.trans sFit),Nat.mod_eq_of_lt (i.isLt.trans_le route.cap)]
    exact off i
  · intro i
    have headNz : 0<g.head.size:=by rw [route.book];have:=i.isLt;omega
    rw [old _ (Or.inr (Or.inr (Or.inr rfl))) headNz,route.book,Bank.read,Fin.val_cast_of_lt (i.isLt.trans sFit),
      Nat.mod_eq_of_lt (i.isLt.trans_le heads)]
    exact site_head L m ok B parts i (route.books i)

end
end Hierarchy.DescentTerminalRowPlan

end OAI
