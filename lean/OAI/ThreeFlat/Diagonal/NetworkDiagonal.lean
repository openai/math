import OAI.ThreeFlat.Diagonal.TemplateDiagonal
import OAI.ThreeFlat.Diagonal.ApproximateNetwork

namespace OAI
/-! # Rank obstruction with the evaluator's addressed trivalent network

The approximated matrix in this statement is the actual contraction of the
shared block network whose pins are the advice and the two external indices.
-/

namespace ThreeFlat.Diagonal

open ApproximatePort BoundaryWire
open scoped BigOperators Classical

variable {F : Type*} [Field F] {chunks a d n t m p teams : ℕ}

/-- The contraction of the block evaluation network with its external
indices set and the endpoint auxiliary words zero. -/
noncomputable def approximatedMatrix (X : BitNetwork F m) (D : Fin d → Bool)
    (select : Fin (t+1) → Fin m → ApproximatePort (Fin chunks) d n a)
    (slot : Fin (t+1) → Fin (n+1) → Fin chunks) (active : Fin (t+1) → Bool)
    (keep : Fin (t+1) → Fin chunks → Bool) :
    Matrix (Bool → Fin chunks → BitString a) (Bool → Fin chunks → BitString a) F := fun x y =>
  (ApproximateNetwork.network select slot active X keep).eval (pinBits D (x,fun _ => false) (y,fun _ => false))

theorem approximatedMatrix_eq (X : BitNetwork F m) (D : Fin d → Bool)
    (select : Fin (t+1) → Fin m → ApproximatePort (Fin chunks) d n a)
    (slot : Fin (t+1) → Fin (n+1) → Fin chunks) (active : Fin (t+1) → Bool)
    (keep : Fin (t+1) → Fin chunks → Bool) (hkeep : ∀ i k, keep i k = true ↔ k ∉ Finset.univ.image (slot i)) :
    approximatedMatrix X D select slot active keep = physicalRun (List.ofFn id) slot active
      (fun i f => catalyst X (select i) D f) := by
  ext x y
  rw [approximatedMatrix, ApproximateNetwork.eval select slot active X keep hkeep]
  simp only [physicalRun, Matrix.submatrix_apply, List.map_ofFn, Function.comp_id]

/-- The trivalent evaluator for all approximated blocks cannot differ from
the genuine chronological tick computation by one identity on external
memory, provided the catalyst evaluation meets the stated rank saving. -/
theorem network_diagonal_gap (N : BitNetwork F p) (X : BitNetwork F m) (D : Fin d → Bool)
    (select : Fin (t+1) → Fin m → ApproximatePort (Fin chunks) d n a)
    (slot : Fin (t+1) → Fin (n+1) → Fin chunks) (active : Fin (t+1) → Bool)
    (keep : Fin (t+1) → Fin chunks → Bool) (hkeep : ∀ i k, keep i k = true ↔ k ∉ Finset.univ.image (slot i))
    (distinct : ∀ i, Function.Injective (slot i))
    (pin : Fin (t+1) → Fin (n+1) → Fin teams → BitString a → BitString a → BitString a → BitString a → Fin p → Bool)
    {w e : ℕ} (ha : a = 2^(w^10-w^4)) (hw : e+8 ≤ w) (hmax : n+1 ≤ w^e)
    (hsave : 2^(w^3)*2^(w^10-w) ≤ a*chunks) (hsteps : t+1 ≤ 2^(w^6)/(n+1))
    (approx : ∀ i f, (catalyst X (select i) D f - (∏ j, ∏ k, N.eval (fixingPins (pin i) f j k)) • 1).rank ≤
      2^(a*chunks-2^(w^3)*2^(w^10-w))) :
    templateRun N (List.ofFn id) slot active pin ≠ 1 + approximatedMatrix X D select slot active keep := by
  rw [templateRun_eq_fixings _ _ _ _ distinct, approximatedMatrix_eq _ _ _ _ _ _ hkeep]
  apply physical_replacement_ne_identity_add (List.ofFn id) slot active _ _ ha hw (Nat.succ_pos _) hmax
  · simpa only [Fintype.card_fin] using hsave
  · simpa only [List.length_ofFn] using hsteps
  · intro i _ f
    rw [fixingWeight_eq_template_product, Fintype.card_fin]
    exact approx i f

end ThreeFlat.Diagonal

end OAI
