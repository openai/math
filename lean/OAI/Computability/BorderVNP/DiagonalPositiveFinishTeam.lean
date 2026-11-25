import OAI.Computability.BorderVNP.DiagonalPositiveFinishClaim
import OAI.Computability.BorderVNP.DiagonalJointReaderValue

/-! # The unique transmitted subtotal bank on a genuine joint private candidate -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction TeamContraction.JointHeader CompactMachine CellMacro.Generator _root_.OAI.Computability.BorderVNP.Cube
open DiagonalResidueRAM (word)
open scoped BigOperators Classical

variable {axes box lanes selectors symbols w T n reserve groups cap dim width : ℕ}
    {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}

/-- A fixed routing, pin and original private candidate as the shared claim is
varied. Every native prefix carries its actual report and builder memory. The
selected operand receipt counts that same source candidate at each possible claim. -/
structure PositiveClaimCandidate (id : TableEntry axes box lanes selectors symbols → ℕ)
    (gen : Fragment IO) (n w : ℕ) (p : (PositiveFields reserve axes groups cap T dim width)) where
  /-- Natural subtotal rows of the original physical source. -/
  rows : Fin T → Fin dim → ℕ
  /-- Physical positive teams at each proposed shared claim. -/
  team : (Fin (T*dim*width) → Bool) → Fin T → PositiveTeam id gen n w
  /-- The ordered owned cells of the actual team preparations. -/
  joined : ∀ raw (a : (u : Fin T) → (team raw u).Prefix),
    JoinedCells (fun u => (team raw u).pub) (fun u => (team raw u).postMemory) (fun u => (team raw u).generated) a
  /-- Native prefixes and private bit vectors at each claim. -/
  candidate : ∀ raw, PositiveAssignment (team raw) (joined raw)
  /-- The selected operand and allocation receipt at each post-cell state. -/
  input : ∀ raw u, let S := team raw u
    let a := (candidate raw).1 u
    let mac := install gen n S.routines
    PositiveFields.FinishInput u rows width S.pub mac (cellBank S.pub mac a.2.val.2.1 a.2.val.2.2) a.2.val.2.2
      (p.withSubtotals raw).tallyWords
  widthFit : width ≤ w
  rowFit : ∀ u c, rows u c < 2^width
  sumFit : ∀ c, ∑ u,rows u c < 2^w

namespace PositiveClaimCandidate

variable {p : (PositiveFields reserve axes groups cap T dim width)} (X : PositiveClaimCandidate id gen n w p)

/-- The shared bit vector of this candidate’s actual subtotal rows. -/
abbrev canonical := PositiveFields.canonicalSubtotals width X.rows

/-- On all actual finishing states, success is equivalent to transmitting the
one true claim. This comparison precedes and is independent of the lead residue. -/
theorem tallyReturns_iff (raw : (Fin (T*dim*width) → Bool)) :
    (∀ u, (X.team raw u).tallyReturns ((X.candidate raw).1 u)) ↔ raw=X.canonical :=
  PositiveFields.finishes_iff (p.withSubtotals raw) X.rows _ _ _ _ (X.input raw) X.widthFit X.rowFit X.sumFit

/-- The original private cell bank at its true reports. -/
noncomputable abbrev canonicalCellWeight := (X.joined X.canonical (X.candidate X.canonical).1).privateWeight (X.candidate X.canonical).2

/-- For this passing private candidate, the full positive predicate forces and
is forced by its canonical raw field. No condition is imposed on residue values. -/
theorem pass_iff (ok : X.canonicalCellWeight ≠ 0) (raw : (Fin (T*dim*width) → Bool)) :
    positivePass (X.team raw) (X.joined raw) (X.candidate raw) ↔ raw=X.canonical := by
  constructor
  · intro accepted
    exact (X.tallyReturns_iff raw).mp accepted.2
  · rintro rfl
    exact ⟨ok,(X.tallyReturns_iff X.canonical).mpr rfl⟩

/-- The selected native finish used by the actual entry reader stores the sum
of this original candidate's counts at every numbered bit of its fixed output. -/
theorem finish_output (raw : (Fin (T*dim*width) → Bool)) (pass : positivePass (X.team raw) (X.joined raw) (X.candidate raw))
    (u : Fin T) (c : Fin dim) (j : ℕ) (hj : j<w) :
    let h := X.input raw u
    ((X.team raw u).finish ((X.candidate raw).1 u) (pass.2 u)).val.2.2
      (h.post.localBase+dim+T*dim+dim+dim+1+(c.val*w+j)) = word w (((∑ v,X.rows v c).testBit j).toNat) := by
  have eq := (X.tallyReturns_iff raw).mp pass.2
  subst raw
  let h := X.input X.canonical u
  obtain ⟨z,_,_,image⟩ := h.complete (PositiveFields.canonical_tallyWords p X.rows) X.rowFit X.sumFit
  have same := PositiveFields.finish_eq ((X.team X.canonical u).finish ((X.candidate X.canonical).1 u) (pass.2 u)) z
  rw [same]
  exact image c j hj

/-- Forget the only returning shared claim while retaining the full source
candidate. The inverse installs the prescribed digits in precisely its native
prefix family, so the reader can reuse the returned memory above. -/
def sourceClaimEquiv {Source : Type*} (A : Source → PositiveClaimCandidate id gen n w p)
    (ok : ∀ a,(A a).canonicalCellWeight ≠ 0) :
    (Σ a : Source, {raw : (Fin (T*dim*width) → Bool) // positivePass ((A a).team raw) ((A a).joined raw) ((A a).candidate raw)}) ≃ Source where
  toFun x := x.1
  invFun a := ⟨a,(A a).canonical,((A a).pass_iff (ok a) _).mpr rfl⟩
  left_inv := by
    rintro ⟨a,raw,h⟩
    exact congrArg (Sigma.mk a) (Subtype.ext (((A a).pass_iff (ok a) _).mp h).symm)
  right_inv _ := rfl

end PositiveClaimCandidate
end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
