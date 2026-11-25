import OAI.ThreeFlat.Diagonal.NavigationDirectory
import OAI.ThreeFlat.Diagonal.CompressorResidentLayout
import OAI.ThreeFlat.RAM.HeaderScanLayout

namespace OAI
/-! # Instantiating the shrinking header, immutable input spans and chronological bump allocator -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan NavigationDirectory
open scoped Fin.NatCast
variable {w : ℕ}

def pointers (K : ℕ) (c : Cursor) (x : Dimensions) : Pointers :=
  let f:=(allocate K c (.shrink x)).words
  ⟨f 1,f 2,f 3,f 4,f 6,f 8,f 11,f 13,f 16,f 18,f 19,f 20,f 23,f 24,f 30,c.header⟩

theorem fields (K : ℕ) (c : Cursor) (x : Dimensions) (i : Fin 34) :
    (allocate K c (.shrink x)).words i.val=headerWord x (pointers K c x) i.val := by
  fin_cases i <;> rfl

structure CursorSpace (cur : Word w) (mem : Memory w) (c : Cursor) (K : ℕ) (x : Dimensions) : Prop where
  header : Scans.Header cur mem c.header 63 (allocate K c (.shrink x)).words
  graph : c.graph+6*x.oldEdges≤c.heap
  widths : c.width+x.oldEdges*x.originalLanes≤c.heap
  counts : c.dense+K*x.motifs≤c.heap
  earlier : c.header+64≤c.heap
  controls : (allocate K c (.shrink x)).next.heap≤cur.val

namespace CursorSpace
variable {cur : Word w} {m : Memory w} {c : Cursor} {K : ℕ} {x : Dimensions}
variable (s : CursorSpace cur m c K x)
set_option quotPrecheck false
local notation "p" => pointers K c x

include s
theorem pristine : Header x p false cur m := by
  refine ⟨s.header.pointer,by change c.header+34≤2^w; have := s.header.fit; omega,?_⟩
  intro i
  apply Fin.ext
  have h := (s.header.values i.val (by have:=i.isLt; omega)).trans (fields K c x i)
  have canon : value x p false i.val = headerWord x p i.val := by
    by_cases e : i.val=27
    · rw [e]; rfl
    · simp [value,selected,e]
  rw [canon,Fin.val_cast_of_lt (by rw [←h]; exact (m _).isLt)]
  exact h

omit s in
theorem allocated (_space : CursorSpace cur m c K x) :
    (p).choices=c.heap ∧ (p).supply=(p).choices+3*x.motifs ∧
    (p).demands=(p).supply+8*x.motifs ∧ (p).split=(p).demands+2*x.motifs ∧
    (p).colors=(p).split+8*x.oldEdges ∧ (p).offsets=(p).colors+x.oldBase ∧
    (p).newGraph=(p).offsets+x.oldBase ∧ (p).keys=(p).newGraph+6*x.newEdges ∧
    (p).newWidths=(p).keys+x.newEdges ∧ (p).costs=(p).newWidths+x.newEdges*x.residual := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem end_lt : (p).newWidths+x.newEdges*x.residual<2^w := by
  have finish : (p).costs≤(allocate K c (.shrink x)).next.heap := by
    change (p).costs≤extraEnd x ((p).costs+2*(x.motifs+1))
    rw [extra_extent]
    omega
  have h := s.allocated.2.2.2.2.2.2.2.2.2
  rw [←h]
  exact (finish.trans s.controls).trans_lt cur.isLt

theorem separation : Separation (w:=w) x p cur.val := by
  obtain ⟨a,b,d,e,f,g,h,i,j,k⟩ := s.allocated
  refine ⟨i.ge,j.ge,s.end_lt,?_⟩
  intro z read
  have stop : (p).newWidths+x.newEdges*x.residual≤cur.val := by
    rw [←k]
    exact (show (p).costs≤extraEnd x ((p).costs+2*(x.motifs+1)) by rw [extra_extent]; omega).trans s.controls
  cases read with
  | current eqv => right; rwa [eqv]
  | header atHdr =>
    left; change c.header≤z ∧ z<c.header+34 at atHdr
    have := s.earlier; omega
  | graph atGraph =>
    left; change c.graph≤z ∧ z<c.graph+6*x.oldEdges at atGraph
    have := s.graph; omega
  | widths atWidths =>
    left; change c.width≤z ∧ z<c.width+x.oldEdges*x.originalLanes at atWidths
    have := s.widths; omega
  | sliced atSplit => left; rcases atSplit with ⟨_,lt⟩; omega
  | colors atColor => left; rcases atColor with ⟨_,lt⟩; omega
  | offsets atOffset => left; rcases atOffset with ⟨_,lt⟩; omega
  | issued atSupply => left; rcases atSupply with ⟨_,lt⟩; omega


end CursorSpace


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
