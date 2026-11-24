import OAI.Computability.VPVNP.ParseGrammar
import OAI.Computability.VPVNP.PairedFamily

/-!
# Integer polynomials in the grammar labels

In §8.1 of *VP and VNP differ over every field*, the label equations (8.1) use
one indeterminate per terminal or ordered binary production. Here `labelQuery`
is the polynomial `Bₓ` read at a specified state. Every parse with `a` leaves
contributes exactly `2a - 1` label factors.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial ParseGrammar

/-- A terminal production is indexed by its state and variable. A binary production
records the parent layer and state, the split, and the two ordered child states. -/
abbrev GrammarLabel (V H : Type*) (n : ℕ) := (H × V) ⊕ (Σ d : Fin n, H × Fin d.val × H × H)

/-- The state table over the integer polynomial ring with distinct indeterminate labels. -/
noncomputable def universalGrammar (V H : Type*) (n : ℕ) :
    ParseGrammar (MvPolynomial (GrammarLabel V H n) ℤ) V H n where
  terminal h v := X (.inl (h, v))
  binary d h b i j := X (.inr ⟨d, h, b, i, j⟩)

variable {V H R : Type*} {n m : ℕ}

/-- The scalar assigned to each production label by a given grammar. -/
def ParseGrammar.labelValue (G : ParseGrammar R V H n) : GrammarLabel V H n → R
  | .inl (h, v) => G.terminal h v
  | .inr ⟨d, h, b, i, j⟩ => G.binary d h b i j

/-- Specialize the universal integer labels to the entries of `G`. -/
noncomputable def ParseGrammar.specializeLabels [CommRing R] (G : ParseGrammar R V H n) :
    MvPolynomial (GrammarLabel V H n) ℤ →+* R := eval₂Hom (Int.castRingHom R) G.labelValue

variable [Fintype V] [Fintype H]

/-- Count all scalar labels, keeping the split index of each layer explicit. -/
theorem card_grammarLabel (n : ℕ) : Fintype.card (GrammarLabel V H n) =
    Fintype.card H * Fintype.card V + (∑ d : Fin n, d.val) * Fintype.card H ^ 3 := by
  simp only [GrammarLabel, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fin, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun d _ ↦ by ring

/-- Substituting the scalar labels commutes with evaluation at each state. -/
theorem ParseGrammar.specialize_universalGrammar [CommRing R] (G : ParseGrammar R V H n)
    (d : Fin n) (h : H) :
    MvPolynomial.map G.specializeLabels ((universalGrammar V H n).eval d h) = G.eval d h := by
  symm
  apply G.eval_eq_of_recurrence
    (fun d h ↦ MvPolynomial.map G.specializeLabels ((universalGrammar V H n).eval d h))
  · intro d h hd
    rw [eval_terminal _ hd]
    simp [universalGrammar, specializeLabels, labelValue]
  · intro d h hd
    rw [eval_binary _ hd]
    simp [universalGrammar, specializeLabels, labelValue]

/-- Specialization of every formal coefficient of the universal grammar. -/
theorem ParseGrammar.specialize_coefficient [CommRing R] (G : ParseGrammar R V H n)
    (d : Fin n) (h : H) (e : V →₀ ℕ) :
    G.specializeLabels (((universalGrammar V H n).eval d h).coeff e) = (G.eval d h).coeff e := by
  rw [← coeff_map, G.specialize_universalGrammar]

/-- The integer coefficient query `Bₓ` of (8.1). At the start state the layer has
value `m - 1`, and the queried polynomial has degree `m` in the paired variables. -/
noncomputable def labelQuery (d : Fin n) (h : H) (x : Fin m → Bool) :
    MvPolynomial (GrammarLabel (Fin m × Bool) H n) ℤ :=
  ((universalGrammar (Fin m × Bool) H n).eval d h).coeff (pairedExponent x)

theorem ParseGrammar.specialize_labelQuery [CommRing R] (G : ParseGrammar R (Fin m × Bool) H n)
    (d : Fin n) (h : H) (x : Fin m → Bool) :
    G.specializeLabels (labelQuery d h x) = (G.eval d h).coeff (pairedExponent x) :=
  G.specialize_coefficient d h (pairedExponent x)

omit [Fintype V] [Fintype H] in
/-- Each tree uses one label per terminal leaf and one per binary internal vertex. -/
theorem universalGrammar_weight_isHomogeneous (d : Fin n) (h : H) (p : OrderedParse V H d.val) :
    ((universalGrammar V H n).weight d h p).IsHomogeneous (2 * d.val + 1) := by
  induction d using (measure (fun d : Fin n ↦ d.val)).wf.induction generalizing h with
  | h d ih =>
    obtain ⟨k, hk⟩ := d
    cases k with
    | zero =>
      cases p with
      | leaf v =>
        rw [weight_leaf]
        exact isHomogeneous_X ℤ (.inl (h, v) : GrammarLabel V H n)
    | succ k =>
      cases p with
      | node b i j l r =>
        let d : Fin n := ⟨k + 1, hk⟩
        rw [weight_node]
        have hl := ih (leftDegree d b) (leftDegree_lt d b) i l
        have hr := ih (rightDegree d b) (rightDegree_lt d b) j r
        have hb := isHomogeneous_X ℤ (.inr ⟨d, h, b, i, j⟩ : GrammarLabel V H n)
        convert (hb.mul hl).mul hr using 1
        · rfl
        · have := split_degrees d b
          change 2 * d.val + 1 = _
          omega

/-- Reading any coefficient in the input variables leaves a homogeneous polynomial
in the production labels. -/
theorem universalGrammar_coeff_isHomogeneous (d : Fin n) (h : H) (e : V →₀ ℕ) :
    (((universalGrammar V H n).eval d h).coeff e).IsHomogeneous (2 * d.val + 1) := by
  rw [eval_eq_sum, coeff_sum]
  refine IsHomogeneous.sum _ _ _ fun p _ ↦ ?_
  rw [coeff_C_mul]
  let P : MvPolynomial V ℤ := (p.leaves.map X).prod
  have hcoeff : ((p.leaves.map (X (R := MvPolynomial (GrammarLabel V H n) ℤ))).prod).coeff e =
      C (P.coeff e) := by
    rw [← coeff_map]
    simp only [P, map_list_prod, List.map_map, Function.comp_def, MvPolynomial.map_X]
  rw [hcoeff]
  simpa using (universalGrammar_weight_isHomogeneous d h p).mul
    (isHomogeneous_C (GrammarLabel V H n) (P.coeff e))

theorem labelQuery_isHomogeneous (d : Fin n) (h : H) (x : Fin m → Bool) :
    (labelQuery d h x).IsHomogeneous (2 * d.val + 1) :=
  universalGrammar_coeff_isHomogeneous d h (pairedExponent x)

end VPVNP
end Computability
end OAI
