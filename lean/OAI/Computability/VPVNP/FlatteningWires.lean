import OAI.Computability.VPVNP.TensorFlatteningPoint

/-!
# Identity wires across a flattening cut

Flattening at one party gives the cut-rank examples of Section 2. A crossing wire
contains a full identity minor. A wire among the other parties contributes one row.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v w

namespace WireTensor

variable {k : Type u} {J : Type v} [Field k] [Fintype J]

section CutRanks

variable [DecidableEq J]

/-- The cut through one endpoint of a wire has an identity minor of its full dimension. -/
theorem flattening_rank_wire_endpoint {a b : J} (hab : a ≠ b) (I : Type w) [Fintype I] :
    (flattening a (wire (k := k) a b I)).rank = Fintype.card I := by
  classical
  let T := wire (k := k) a b I
  let row (i : I) : T.Basis a := (fun _ ↦ i, fun _ ↦ i)
  let col (i : I) : OtherBasis a T.Basis := fun _ ↦ (fun _ ↦ i, fun _ ↦ i)
  let e : T.Basis a ≃ I :=
    { toFun := fun x ↦ x.1 rfl
      invFun := row
      left_inv := fun x ↦ by
        apply Prod.ext
        · funext h
          rfl
        · funext h
          exact (hab h).elim
      right_inv := fun _ ↦ rfl }
  have hm : (flattening a T).submatrix row col = 1 := by
    ext i j
    have hb := joinBasis_other a (row i) (col j) ⟨b, Ne.symm hab⟩
    change (if (joinBasis a (row i) (col j) a).1 rfl = (joinBasis a (row i) (col j) b).2 rfl
      then (1 : k) else 0) = _
    rw [joinBasis_self, hb]
    simp [row, col, Matrix.one_apply]
  apply le_antisymm
  · exact (Matrix.rank_le_card_height (flattening a T)).trans_eq (Fintype.card_congr e)
  · simpa [hm] using Matrix.rank_submatrix_le (flattening a T) row col

/-- If the cut party meets neither endpoint, a wire of positive dimension has
one row and contains a nonzero entry. -/
theorem flattening_rank_wire_away {a b c : J} (hca : c ≠ a) (hcb : c ≠ b)
    (I : Type w) [Fintype I] [Nonempty I] :
    (flattening c (wire (k := k) a b I)).rank = 1 := by
  classical
  let T := wire (k := k) a b I
  let i : I := Classical.choice ‹Nonempty I›
  let row (_ : Fin 1) : T.Basis c := (fun _ ↦ i, fun _ ↦ i)
  let col (_ : Fin 1) : OtherBasis c T.Basis := fun _ ↦ (fun _ ↦ i, fun _ ↦ i)
  let hu : Unique (T.Basis c) :=
    { default := row 0
      uniq := fun x ↦ by
        apply Prod.ext
        · funext h
          exact (hca h).elim
        · funext h
          exact (hcb h).elim }
  have hm : (flattening c T).submatrix row col = 1 := by
    ext x y
    have ha := joinBasis_other c (row x) (col y) ⟨a, Ne.symm hca⟩
    have hb := joinBasis_other c (row x) (col y) ⟨b, Ne.symm hcb⟩
    change (if (joinBasis c (row x) (col y) a).1 rfl = (joinBasis c (row x) (col y) b).2 rfl
      then (1 : k) else 0) = _
    rw [ha, hb]
    simp [col, Matrix.one_apply, Subsingleton.elim x y]
  apply le_antisymm
  · simpa using Matrix.rank_le_card_height (flattening c T)
  · simpa [hm] using Matrix.rank_submatrix_le (flattening c T) row col

/-- A positive-dimensional identity wire has its full rank across the cut
and rank one when both endpoints lie on the same side. -/
theorem flattening_rank_wire (a b c : J) (I : Type w) [Fintype I] [Nonempty I] :
    (flattening c (wire (k := k) a b I)).rank =
      if (c = a ∧ c ≠ b) ∨ (c ≠ a ∧ c = b) then Fintype.card I else 1 := by
  classical
  by_cases hca : c = a
  · subst c
    by_cases hab : a = b
    · subst b
      simp only [ne_self_iff_false, and_false, false_and, or_self, ite_false]
      let e : Fin 1 ↪ I := ⟨fun _ ↦ Classical.choice ‹Nonempty I›, fun _ _ _ ↦ Subsingleton.elim _ _⟩
      have hl := flattening_rank_mono a ((wire_restricts_of_embedding (k := k) a a e).trans
        (wire_one a a).2)
      have hu := flattening_rank_mono a (unit_restricts_loop (k := k) a I)
      rw [flattening_unit_rank] at hl hu
      exact le_antisymm hu hl
    · simpa [hab] using flattening_rank_wire_endpoint (k := k) hab I
  · by_cases hcb : c = b
    · subst c
      have hs := wire_swap (k := k) a b I
      have he := le_antisymm (flattening_rank_mono b hs.2) (flattening_rank_mono b hs.1)
      simpa [hca] using he.trans (flattening_rank_wire_endpoint hca I)
    · simpa [hca, hcb] using flattening_rank_wire_away (k := k) hca hcb I

end CutRanks

open scoped Classical

/-- Binary wires give exactly the cut distance at the flattening spectral point. -/
theorem flatteningPoint_wireDistance [Nontrivial J] (c a b : J) :
    (flatteningPoint (k := k) c).wireDistance a b =
      if (c = a ∧ c ≠ b) ∨ (c ≠ a ∧ c = b) then 1 else 0 := by
  classical
  change Real.log ((flatteningPoint (k := k) c).value (wire a b (Fin 2)) : ℝ) / Real.log 2 = _
  rw [coe_flatteningPoint_value, flattening_rank_wire]
  split_ifs
  · simp [Real.log_pos (show (1 : ℝ) < 2 by norm_num) |>.ne']
  · simp

end WireTensor

end VPVNP
end Computability
end OAI
