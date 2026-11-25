import OAI.ThreeFlat.Diagonal.CompressorSplitRows

namespace OAI
/-! # Restoring the old graph and its split displacement across the ordered scratch region -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan
variable {B H : Type} [AddCommGroup H] {w N t l : ℕ} {S : Graph.Stage}
variable {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors}
variable {b : B ≃ Fin N} {p : Pointers} {cell : Word w} {m alt : Memory w}
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ}
local notation "C" => incoming S N p

/-- Exactly the spans preceding the six shrinking sweeps. The old graph and raw pins may
be arbitrarily positioned below them. -/
structure Fresh (x : Dimensions) (p : Pointers) (control : ℕ) : Prop where
  oldGraph : p.oldGraph+6*x.oldEdges≤p.demands
  oldWidths : p.oldWidths+x.oldEdges*x.originalLanes≤p.demands
  header : p.ownHeader+64≤p.demands
  demandEnd : p.demands+2*x.motifs≤p.split
  splitEnd : p.split+8*x.oldEdges≤p.colors
  colorEnd : p.colors+x.oldBase≤p.offsets
  offsetEnd : p.offsets+x.oldBase≤p.newGraph
  high : p.newGraph≤control

theorem CursorSpace.fresh {csr : NavigationDirectory.Cursor} {K : ℕ} {z : Dimensions}
    (s : CursorSpace cell m csr K z) : Fresh z (pointers K csr z) cell.val := by
  obtain ⟨a,b,d,e,f,g,h,i,j,k⟩:=s.allocated
  have graph:=s.graph
  have widths:=s.widths
  have head:=s.earlier
  have tail : (pointers K csr z).costs≤(NavigationDirectory.allocate K csr (.shrink z)).next.heap := by
    change _≤extraEnd z ((pointers K csr z).costs+2*(z.motifs+1))
    rw [extra_extent]; omega
  have ctrl:=s.controls
  refine ⟨?_,?_,?_,e.ge,f.ge,g.ge,h.ge,?_⟩
  · change csr.graph+6*z.oldEdges≤_;omega
  · change csr.width+z.oldEdges*z.originalLanes≤_;omega
  · change csr.header+64≤_;omega
  · omega

local notation "physicalDims" => dims S N t l

omit [AddCommGroup H] in
theorem Old.frame (h : Old S P b p cell prior m) (space : Fresh physicalDims p cell.val)
    (agree : agreesOutside p.demands p.newGraph alt m) : Old S P b p cell prior alt := by
  have ctrl : alt cell.val=m cell.val := agree _ (.inr space.high)
  have hr : Header physicalDims p false cell alt := by
    refine ⟨?_,h.header.safe,?_⟩
    · rw [ctrl];exact h.header.pointer
    · intro i
      rw [agree _ (.inl (by have := i.isLt;have := space.header;omega))]
      exact h.header.words i
  refine ⟨hr,h.stored.frame ?_ ?_,h.graphFits⟩
  · intro z low high
    exact congrArg Fin.val (agree z (.inl (high.trans_le space.oldGraph)))
  · intro z low high
    exact congrArg Fin.val (agree z (.inl (high.trans_le space.oldWidths)))

theorem smallerFrame {lo count : ℕ} (_s : Fresh physicalDims p cell.val) (left : p.demands≤lo)
    (right : lo+count≤p.newGraph) (agree : agreesOutside lo (lo+count) alt m) :
    agreesOutside p.demands p.newGraph alt m := by
  intro a outside
  exact agree a (outside.imp (fun h=>h.trans_le left) (fun h=>right.trans h))

omit [AddCommGroup H] in
theorem Sliced.frame (h : Sliced S P b p cell prior m) (s : Fresh physicalDims p cell.val) {start size : ℕ}
    (lower : p.split+8*(physicalDims).oldEdges≤ start) (upper : start+size≤p.newGraph)
    (frame : agreesOutside start (start+size) alt m) : Sliced S P b p cell prior alt := by
  have low:=s.demandEnd
  have old:=h.toOld.frame s (smallerFrame s (by omega) upper frame)
  refine ⟨old,h.splitFits,?_⟩
  intro v rev j
  have col : (if rev then 4 else 0)+j.val<8 := by
    cases rev <;> have:=j.isLt <;> simp <;> omega
  have idx : SlotImage.ordinal b v<(C).rows := SlotImage.ordinal_lt b v
  have mul:=Nat.mul_le_mul_left (C).rows col
  rw [Nat.mul_succ] at mul
  have raw:=SlotImage.cell_range h.stored v rev 2
  have graph := s.oldGraph
  have rows : (C).rows = (physicalDims).oldEdges := rfl
  have graphBase : (C).graph = p.oldGraph := rfl
  have splitBefore : p.split + (C).rows * ((if rev then 4 else 0) + j.val) +
      SlotImage.ordinal b v < start := by omega
  have cellBefore : SlotImage.cell C b v rev 2 < start := by omega
  rw [frame _ (.inl splitBefore),frame _ (.inl cellBefore)]
  exact h.split v rev j


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
