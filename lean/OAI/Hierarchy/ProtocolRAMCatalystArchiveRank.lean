import OAI.Hierarchy.ProbeCatalystArchiveRows
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Numbering the padded, public reserve positions before the calendar runs -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar
open scoped Classical BigOperators
variable {count payload : ℕ}

section
variable (c : Mesh) (issued : Attempt→Entry count payload)

def atTime (t : Fin (events c).length) := eventEntry issued ((events c).get t)

def recordCount := ∑ t,(atTime c issued t).rows

def rank : (Σ t,Fin (atTime c issued t).rows) ≃ Fin (recordCount c issued) := finSigmaFinEquiv

end

/-- An offset into one original event's owner or signed debit column. The
calendar rank is independent of the memory contents. -/
def sourceAt (c : Mesh) (issued : Attempt→Entry count payload) (base : Event→ℕ)
    (i : Fin (recordCount c issued)) :=
  let z := (rank c issued).symm i
  base ((events c).get z.1)+z.2.val

/-- Only attempts have recorded owner and amount words. -/
def rowArity (rows : Attempt→ℕ) : Event→ℕ
  | .attempt a => rows a
  | .feed _ => 0

def rowOnlyCount (c : Mesh) (rows : Attempt→ℕ) : ℕ :=
  ∑ t : Fin (events c).length,rowArity rows ((events c).get t)

theorem rowOnlyCount_le (c : Mesh) (rows : Attempt→ℕ) (limit : ℕ) (admit : ∀a,rows a≤limit) :
    rowOnlyCount c rows≤fuel c*limit := by
  calc
    _ ≤ ∑ _t : Fin (events c).length,limit := by
      apply Finset.sum_le_sum
      intro t _
      cases (events c).get t with
      | attempt a => exact admit a
      | feed _ => exact Nat.zero_le _
    _ = _ := by simp [event_count,fuel]

private def packedOffset (c : Mesh) (width : Fin (events c).length→ℕ)
    (base : Event→ℕ) (i : Fin (∑ t,width t)) : ℕ :=
  let e : (Σ t,Fin (width t)) ≃ Fin (∑ t,width t) := finSigmaFinEquiv
  let z:=e.symm i
  base ((events c).get z.1)+z.2.val

/-- The pointer for a public occurrence rank is computed without inspecting
any historical owner, debit, or permutation word. -/
def rowOnly (c : Mesh) (rows : Attempt→ℕ) (base : Event→ℕ) (i : Fin (rowOnlyCount c rows)) : ℕ :=
  packedOffset c (fun t=>rowArity rows ((events c).get t)) base i

private theorem rowShape_eq {count payload : ℕ} (c : Mesh) (issued : Attempt→Entry count payload)
    (rows : Attempt→ℕ) (same : ∀a,(issued a).rows=rows a) :
    (fun t=>(atTime c issued t).rows)=(fun t=>rowArity rows ((events c).get t)) := by
  funext t
  change (eventEntry issued ((events c).get t)).rows=_
  cases (events c).get t with
  | attempt a => exact same a
  | feed _ => rfl

theorem recordCount_rowOnly {count payload : ℕ} (c : Mesh) (issued : Attempt→Entry count payload)
    (rows : Attempt→ℕ) (same : ∀a,(issued a).rows=rows a) :
    recordCount c issued=rowOnlyCount c rows :=
  congrArg (fun width : Fin (events c).length→ℕ => ∑ t,width t) (rowShape_eq c issued rows same)

private theorem packedOffset_cast (c : Mesh) (s t : Fin (events c).length→ℕ) (eq : s=t)
    (base : Event→ℕ) (j : Fin (∑ i,s i)) (bound : (∑ i,s i)=∑ i,t i) :
    packedOffset c s base j=packedOffset c t base (Fin.cast bound j) := by
  subst t
  rfl

theorem sourceAt_eq_rowOnly {count payload : ℕ} (c : Mesh) (issued : Attempt→Entry count payload)
    (rows : Attempt→ℕ) (same : ∀a,(issued a).rows=rows a) (base : Event→ℕ)
    (i : Fin (recordCount c issued)) :
    sourceAt c issued base i = rowOnly c rows base (Fin.cast (recordCount_rowOnly c issued rows same) i) :=
  packedOffset_cast c _ _ (rowShape_eq c issued rows same) base i _

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
