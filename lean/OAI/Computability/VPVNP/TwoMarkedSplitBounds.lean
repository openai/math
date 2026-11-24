import OAI.Computability.VPVNP.MarkedEndpointOperation
import OAI.Computability.VPVNP.MarkedSplitBound

/-!
# Endpoint estimates for the children of an exterior split

The second marked index is held in the background when applying the local
operations of Appendix A.2 to a child from Appendix A.3.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor.TwoMarkedNode

open scoped Classical
open ExteriorLevels Lemmata.FockCircuits

universe u v
variable {k : Type u} {J : Type v} [Field k] [Fintype J]
variable {I K H : Type} [Fintype I] [Fintype K] [Fintype H]

/-- Regroup the second marked index with the background so that the child
has precisely the three movable roles used in the one-mark exterior split. -/
theorem child_splitMarkedTerm_mutual (W : TwoMarkedNode k J I K) (s p x y : J)
    (op : H → H → I → I → k) :
    let P := (W.child s p op).place x y
    let V := splitMarkedTerm (fun j => W.Basis j × (j = y → K)) I H x s p
      (holdSecond W.Basis I K W.coeff y) (fun i j β α => op β α i j)
    Restricts P V ∧ Restricts V P := by
  let P := (W.child s p op).place x y
  let V := splitMarkedTerm (fun j => W.Basis j × (j = y → K)) I H x s p
    (holdSecond W.Basis I K W.coeff y) (fun i j β α => op β α i j)
  let e (j : J) : V.Basis j ≃ P.Basis j :=
    { toFun z := ((z.1.1, z.2 (some false), z.2 (some true)), z.2 none, z.1.2)
      invFun z := ((z.1.1, z.2.2), fun r => match r with
        | none => z.2.1
        | some false => z.1.2.1
        | some true => z.1.2.2)
      right_inv _ := rfl
      left_inv z := by
        refine Prod.ext ?_ ?_
        · rfl
        funext r
        rcases r with _ | (_ | _) <;> rfl }
  exact restricts_of_reindex e (fun _ => rfl)

/-- The ordinary endpoint bound uses the exterior level itself as the
identity wire for either child. -/
theorem value_exteriorChild_same_le {q : ℕ} (W : TwoMarkedNode k J (Fin q) K)
    (F : SpectralPoint k J) (A B : Bool → J) (b : ℕ) (hbq : b < q) (s i j : Bool) :
    (F.value ((W.exteriorChild (A false) (A true) b s).place (A i) (B j)) : ℝ) ≤
      (q.choose b : ℝ) ^ F.wireDistance (A false) (A true) *
        (F.value (W.place (A i) (B j)) : ℝ) := by
  have hi : A i = A false ∨ A i = A true := by cases i <;> simp
  have hH : 0 < Fintype.card (Level q b) := by
    rw [card_level]
    exact Nat.choose_pos hbq.le
  simpa only [exteriorChild, card_level, mul_comm] using
    W.value_child_same_le (exteriorOperator b s) F (A false) (A true) (A i) (B j) hi hH

private theorem level_nonempty {q b : ℕ} (h : b ≤ q) : Nonempty (Level q b) :=
  Fintype.card_pos_iff.mp (by simpa only [card_level] using Nat.choose_pos h)

/-- At the column endpoint the positive branch is supplied from the row
endpoint through the level one degree higher. -/
theorem value_exteriorChild_plus_le {q : ℕ} (W : TwoMarkedNode k J (Fin q) K)
    (F : SpectralPoint k J) (A B : Bool → J) (b : ℕ) (hbq : b < q) (j : Bool) :
    (F.value ((W.exteriorChild (A false) (A true) b true).place (A false) (B j)) : ℝ) ≤
      (q.choose (b+1) : ℝ) ^ F.wireDistance (A false) (A true) *
        (F.value (W.place (A true) (B j)) : ℝ) := by
  have : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  have : Nonempty (Level q b) := level_nonempty hbq.le
  have : Nonempty (Level q (b+1)) := level_nonempty hbq
  let op := exteriorOperator (k := k) (q := q) b true
  have hc := F.value_eq_of_mutual (W.child_splitMarkedTerm_mutual (A false) (A true)
    (A false) (B j) op)
  have hp := F.value_eq_of_mutual (twoMarked_first_mutual W.Basis (Fin q) K W.coeff (A true) (B j))
  change (F.value ((W.child (A false) (A true) op).place (A false) (B j)) : ℝ) ≤
    _ * (F.value (twoMarked W.Basis (Fin q) K W.coeff (A true) (B j)) : ℝ)
  rw [hc, hp]
  have h := F.value_splitMarkedTerm_le_plus (fun p => W.Basis p × (p = B j → K))
    (Fin q) (Level q b) (Level q (b+1)) (A false) (A false) (A true) (A true)
    (holdSecond W.Basis (Fin q) K W.coeff (B j)) (fun i l β α => op β α i l)
    (fun i α z => entry k (Fock.create k i) z α)
    (fun l β z => entry k (Fock.contract k l) β z)
    (fun _ _ _ _ => by simp [op, exteriorOperator, mul_comm])
  simpa only [card_level, F.wireDistance_self, Real.rpow_zero, one_mul, mul_comm] using h

/-- At the row endpoint the negative branch is supplied from the column
endpoint through the level one degree lower. -/
theorem value_exteriorChild_minus_le {q : ℕ} (W : TwoMarkedNode k J (Fin q) K)
    (F : SpectralPoint k J) (A B : Bool → J) (b : ℕ) (hbq : b < q) (j : Bool) :
    (F.value ((W.exteriorChild (A false) (A true) b false).place (A true) (B j)) : ℝ) ≤
      (q.choose (b-1) : ℝ) ^ F.wireDistance (A false) (A true) *
        (F.value (W.place (A false) (B j)) : ℝ) := by
  have : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  have : Nonempty (Level q b) := level_nonempty hbq.le
  have : Nonempty (Level q (b-1)) := level_nonempty (by omega)
  let op := exteriorOperator (k := k) (q := q) b false
  have hc := F.value_eq_of_mutual (W.child_splitMarkedTerm_mutual (A false) (A true)
    (A true) (B j) op)
  have hp := F.value_eq_of_mutual (twoMarked_first_mutual W.Basis (Fin q) K W.coeff (A false) (B j))
  change (F.value ((W.child (A false) (A true) op).place (A true) (B j)) : ℝ) ≤
    _ * (F.value (twoMarked W.Basis (Fin q) K W.coeff (A false) (B j)) : ℝ)
  rw [hc, hp]
  have h := F.value_splitMarkedTerm_le_minus (fun p => W.Basis p × (p = B j → K))
    (Fin q) (Level q b) (Level q (b-1)) (A true) (A false) (A true) (A false)
    (holdSecond W.Basis (Fin q) K W.coeff (B j)) (fun i l β α => op β α i l)
    (fun l α z => entry k (Fock.contract k l) z α)
    (fun i β z => entry k (Fock.create k i) β z)
    (fun _ _ _ _ => by simp [op, exteriorOperator, mul_comm])
  simpa only [card_level, F.wireDistance_self, Real.rpow_zero, one_mul, mul_comm] using h

end WireTensor.TwoMarkedNode

end VPVNP
end Computability
end OAI
