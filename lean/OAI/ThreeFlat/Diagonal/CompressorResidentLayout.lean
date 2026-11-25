import OAI.ThreeFlat.Diagonal.CompressorResidentInput

namespace OAI
/-! # Concrete successor write intervals and the recorded shrink-step input frame -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan
open scoped Fin.NatCast
variable {w : ℕ}

structure Separation (x : Dimensions) (p : Pointers) (current : ℕ) : Prop where
  graphKey : p.newGraph+6*x.newEdges≤p.keys
  keyWidth : p.keys+x.newEdges≤p.newWidths
  safe : p.newWidths+x.newEdges*x.residual<2^w
  «protected» : ∀ a,Read x p current a → a<p.newGraph ∨ p.newWidths+x.newEdges*x.residual≤a

variable {x : Dimensions} {p : Pointers} {cell : Word w} {a : ℕ} {m alt : Memory w}

theorem Separation.graphEnd (s : Separation (w:=w) x p cell.val) : p.newGraph+6*x.newEdges<2^w := by
  have := s.graphKey; have := s.keyWidth; have := s.safe; omega

theorem Separation.keyEnd (s : Separation (w:=w) x p cell.val) : p.keys+x.newEdges<2^w := by
  have := s.keyWidth; have := s.safe; omega

theorem Separation.agree (s : Separation (w:=w) x p cell.val) (start size : ℕ)
    (low : p.newGraph≤ start) (upper : start+size≤p.newWidths+x.newEdges*x.residual)
    (agrees : agreesOutside start (start+size) alt m) (r : Read x p cell.val a) : alt a=m a := by
  exact agrees _ ((s.protected a r).imp (fun lt=>lt.trans_le low) (fun le=>upper.trans le))

theorem Separation.fill (s : Separation (w:=w) x p cell.val) (start size : ℕ)
    (low : p.newGraph≤ start) (upper : start+size≤p.newWidths+x.newEdges*x.residual)
    (file : ℕ → Word w) (m : Memory w) (a : ℕ) (hr : Read x p cell.val a) :
    fillSegment start size file m a=m a := by
  apply s.agree start size low upper _ hr
  intro a out
  rcases out with lo|hi
  · simp [fillSegment,show ¬start≤a by omega]
  · simp [fillSegment,show ¬a<start+size by omega]


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
