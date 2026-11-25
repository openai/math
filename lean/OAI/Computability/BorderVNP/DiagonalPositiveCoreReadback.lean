import OAI.Computability.BorderVNP.DiagonalPositiveCoreReports
import OAI.Computability.BorderVNP.DiagonalTypedTallyReader
import OAI.Computability.BorderVNP.DiagonalJoinedPrivateBank

/-! # Exact readback on the genuine native memory of an initially unchecked assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.UncheckedCandidate

open VPVNP.BurstRAM TeamContraction.JointHeader DiagonalTallyCellReports CellMacro.Generator _root_.OAI.Computability.BorderVNP.Cube
open DiagonalResidueRAM
open scoped BigOperators Classical

variable {axes box lanes selectors symbols T n w reserve groups cap dim width : ℕ}
    {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}
    {p : PositiveFields reserve axes groups cap T dim width}
    (X : UncheckedCandidate id gen n w T dim width) (H : X.Completion p)
    (r : NativeReports X.assigned) (raw : Fin (T*dim*width) → Bool)
    (ok : positivePass (X.team r raw) (X.joined r raw) (X.candidate r raw))

include H ok in
/-- On a physically accepted term each true private validator has positive
sign. In particular the integer factor of the joint private sum is exactly
one even if the subsequent lead coefficient is zero. -/
theorem Completion.privateWeight_one :
    (X.joined r raw (X.candidate r raw).1).privateWeight (X.candidate r raw).2=1 := by
  apply JoinedCells.privateWeight_one _ _ _ ok.1
  intro c
  let image := X.image r raw
  obtain ⟨⟨u,i⟩,rfl⟩ := image.number.surjective c
  rw [image.directory u i]
  exact (H.core u ((X.assigned u).get i) (List.get_mem _ _)).unsigned

/-- The actual `PositiveTeam.finish` on an arbitrary returning original
assignment has written the true source sums at its selected output address. -/
theorem Completion.finish_output (u : Fin T) (c : Fin dim) (j : ℕ) (hj : j<w) :
    let input := H.input raw u
    ((X.team r raw u).finish ((X.candidate r raw).1 u) (ok.2 u)).val.2.2
      (input.post.localBase+dim+T*dim+dim+dim+1+(c.val*w+j)) = word w (((∑ t,H.rows t c).testBit j).toNat) := by
  have same := (((X.completed H).pass_iff r raw).mp ok).1
  subst r
  exact (X.completed H).atReports.finish_output raw ok u c j hj

/-- Read the same physical bank in the typed tally order used by the true
lead reader. Physical owner rows need only agree with the original tally
after summation over their owners. -/
theorem Completion.tally_readback {parameters scalars B : ℕ}
    (tally : Diagonal.Tally (Fin T) (Fin parameters) (Fin scalars) B)
    (index : Fin (parameters+scalars) ≃ Fin dim) (ordered : ∀ i,(index i).val=i.val)
    (totals : ℕ) (u : Fin T) (base : (H.input raw u).post.localBase+dim+T*dim+dim+dim+1=totals)
    (original : ∀ c, ∑ t,H.rows t (index c)=∑ t,DiagonalTallyRAM.tallyRow tally t c)
    (c : Fin (parameters+scalars)) (j : ℕ) (hj : j<w) :
    ((X.team r raw u).finish ((X.candidate r raw).1 u) (ok.2 u)).val.2.2 (totals+(c.val*w+j)) =
      word w (((∑ t,DiagonalTallyRAM.tallyRow tally t c).testBit j).toNat) := by
  have h := Completion.finish_output X H r raw ok u (index c) j hj
  simpa only [base,ordered,original] using h

end RoutingISA.Evaluator.UncheckedCandidate

end BorderVNP
end Computability
end OAI
