import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementOrder
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementContourWord
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchFormula

/-! # Direct and trivalent terms in a patch record's tree list

The nonroot input labels and the distinguished output are read from the
record's actual spanning-tree contour. The coefficients use the shared old
table variables at the original width.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators
namespace PortGraph.PatchShape

open PlanarPatch UniformDecorations

variable {K : ℕ} (R : PatchShape K) (hc : R.InternallyConnected)

def contourSlots {b : ℕ} (h : Fintype.card R.Stub = b+1) : R.Stub ≃ Fin (b+1) :=
  (R.contourStubEquiv hc).symm.trans (finCongr h)

def entryExponent (K : ℕ) := max (5*K+5) (20*(2*(5*K)+1)+7)

/-- One genuine term selected by patch replacement. The direct term has one
role. The large term carries the actual pruned ordered tensor tree. -/
inductive RecordTerm (w : ℕ) (F : Type) [Field F]
  | direct (small : Fintype.card R.Stub ≤ 3)
  | pruned {b : ℕ} (total : Fintype.card R.Stub = b+1) (large : 3 ≤ b)
      (t : TrivalentTree (MvPolynomial (Address w) F) (fun _ : R.Stub => 2^w) (2^w))
      (labels : t.labels = (List.finRange b).map (fun i => (R.contourSlots hc total).symm i.castSucc))
      (bound : t.Bounded (2^(8*w)))
      (count : t.vertices + 2 = Fintype.card R.Stub)
      (cost : t.FormulaBound (2^(entryExponent K*(w+1))))

variable {R hc} {w : ℕ} {F : Type} [Field F]

/-- Read the direct or tree contraction on a legal tuple of original-width stubs. -/
def RecordTerm.value (u : R.RecordTerm hc w F) (x : R.Stub → Bits w) : MvPolynomial (Address w) F :=
  match u with
  | .direct _ => R.oldValue (fun θ y => MvPolynomial.X ⟨θ,y⟩) x
  | .pruned total _ t _ _ _ _ => t.eval x (x ((R.contourSlots hc total).symm (Fin.last _)))

end PortGraph.PatchShape

end

end SpectralBooks
end LinearAlgebra
end OAI
