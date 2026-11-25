import OAI.ThreeFlat.Diagonal.HistoryBatchRows
import OAI.ThreeFlat.Diagonal.MotifSelectorChecks

namespace OAI
/-! # Applying the two-run address generator to actual selector and tile batches -/

namespace ThreeFlat.Diagonal.HistoryContraction.Tree.BatchRows

open MotifOrderedCells MotifOuterTerms MotifSelectorChecks
open private component_left component_right from OAI.ThreeFlat.Diagonal.MotifSelectorChecks
open private pieces_left pieces_right from OAI.ThreeFlat.Diagonal.MotifOrderedCells
open scoped Classical
noncomputable section

variable {F : Type*} [CommRing F] {r s k e d b : ℕ}

def lutSize (b : ℕ) : Size := ⟨b,2^b*(b+1),2^b⟩
def compSize {p : ℕ} (C : BitNetwork F p) : Size := ⟨p,C.cells,C.internal⟩

private theorem split {r s a b : ℕ} {N : Fin (r+s) → ℕ}
    (lhs : ∀ i : Fin r, N (i.castAdd s)=a) (rhs : ∀ j : Fin s, N (Fin.natAdd r j)=b) :
    ∀ i, N i = if i.val<r then a else b := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_)
  · simpa [i.isLt] using lhs i
  · simpa using rhs j

/-- The `r` local Boolean LUTs are followed by `s` physical compactor
leaves, one per alphabet symbol, each with the same dyadic width. -/
theorem checks_sizes (good : (Fin b → Bool) → Prop) (letter : (Fin b → Bool) → Fin s)
    (C : BitNetwork F (r+(r+r))) (z : Histogram (Fin s) r) :
    let X := MotifSelectorChecks.components good letter C z
    Sizes (fun i => (X i).net) (lutSize (b+s)) (compSize C) := by
  dsimp only
  constructor <;> apply split <;> intro j
  · simpa only [lutSize,compSize,ConstantKernelLUT.network_cells,ConstantKernelLUT.network_internal] using
      congrArg (fun x : MotifSelectorChecks.Component F (r*s) (r*b) => x.width) (component_left good letter C z j)
  · simpa only [lutSize,compSize,ConstantKernelLUT.network_cells,ConstantKernelLUT.network_internal] using
      congrArg (fun x : MotifSelectorChecks.Component F (r*s) (r*b) => x.width) (component_right good letter C z j)
  · simpa only [lutSize,compSize,ConstantKernelLUT.network_cells,ConstantKernelLUT.network_internal] using
      congrArg (fun x : MotifSelectorChecks.Component F (r*s) (r*b) => x.net.cells) (component_left good letter C z j)
  · simpa only [lutSize,compSize,ConstantKernelLUT.network_cells,ConstantKernelLUT.network_internal] using
      congrArg (fun x : MotifSelectorChecks.Component F (r*s) (r*b) => x.net.cells) (component_right good letter C z j)
  · simpa only [lutSize,compSize,ConstantKernelLUT.network_cells,ConstantKernelLUT.network_internal] using
      congrArg (fun x : MotifSelectorChecks.Component F (r*s) (r*b) => x.net.internal) (component_left good letter C z j)
  · simpa only [lutSize,compSize,ConstantKernelLUT.network_cells,ConstantKernelLUT.network_internal] using
      congrArg (fun x : MotifSelectorChecks.Component F (r*s) (r*b) => x.net.internal) (component_right good letter C z j)

/-- Each tile copy uses exactly the same LUT record size, even if the
concrete coefficients in its archived table depend on the copy ordinal. -/
theorem payload_sizes (tiles : Fin r → (Fin (b+(e*d+e*d)) → Bool) → F)
    (C : BitNetwork F ((r*d)+(r*d+r*d))) :
    let X := pieces tiles C
    Sizes (fun i => (X i).N) (lutSize (b+(e*d+e*d))) (compSize C) := by
  dsimp only
  constructor <;> apply split <;> intro j
  · simpa only [lutSize,compSize,ConstantKernelLUT.network_cells,ConstantKernelLUT.network_internal] using
      congrArg (fun x : MotifOrderedCells.Piece F (e*(r*d)+e*(r*d)) (r*b+e*(r*d)) => x.width) (pieces_left tiles C j)
  · simpa only [lutSize,compSize,ConstantKernelLUT.network_cells,ConstantKernelLUT.network_internal] using
      congrArg (fun x : MotifOrderedCells.Piece F (e*(r*d)+e*(r*d)) (r*b+e*(r*d)) => x.width) (pieces_right tiles C j)
  · simpa only [lutSize,compSize,ConstantKernelLUT.network_cells,ConstantKernelLUT.network_internal] using
      congrArg (fun x : MotifOrderedCells.Piece F (e*(r*d)+e*(r*d)) (r*b+e*(r*d)) => x.N.cells) (pieces_left tiles C j)
  · simpa only [lutSize,compSize,ConstantKernelLUT.network_cells,ConstantKernelLUT.network_internal] using
      congrArg (fun x : MotifOrderedCells.Piece F (e*(r*d)+e*(r*d)) (r*b+e*(r*d)) => x.N.cells) (pieces_right tiles C j)
  · simpa only [lutSize,compSize,ConstantKernelLUT.network_cells,ConstantKernelLUT.network_internal] using
      congrArg (fun x : MotifOrderedCells.Piece F (e*(r*d)+e*(r*d)) (r*b+e*(r*d)) => x.N.internal) (pieces_left tiles C j)
  · simpa only [lutSize,compSize,ConstantKernelLUT.network_cells,ConstantKernelLUT.network_internal] using
      congrArg (fun x : MotifOrderedCells.Piece F (e*(r*d)+e*(r*d)) (r*b+e*(r*d)) => x.N.internal) (pieces_right tiles C j)


end
end ThreeFlat.Diagonal.HistoryContraction.Tree.BatchRows

end OAI
