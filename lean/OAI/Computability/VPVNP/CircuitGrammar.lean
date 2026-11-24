import OAI.Computability.VPVNP.CircuitGrammarSpan
import OAI.Computability.VPVNP.ParseGrammar

/-!
# Graded parse labels for exact circuits

An exact circuit determines one assignment of the labels of the grammar of Section 8.1
of *VP and VNP differ over every field*. This assignment works simultaneously for all
homogeneous pieces up to the prescribed cutoff and for all gate, variable and output
states. It allows arbitrary field constants and does not require homogeneous intermediate
gate computations.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial ParseGrammar

variable {R V H : Type*} [CommRing R] [Fintype V] [Fintype H] {n D : ℕ}

omit [Fintype V] in
private theorem Circuit.exists_production_labels (c : Circuit R V n)
    (state : H → Circuit.GrammarSlots V n) (surj : Function.Surjective state)
    (d : Fin D) (h : H) (hd : d.val ≠ 0) :
    ∃ w : Fin d.val → H → H → R, homogeneousComponent (d.val + 1) (c.slotPolynomial (state h)) =
      ∑ b, ∑ i, ∑ j, C (w b i j) *
        homogeneousComponent ((leftDegree d b).val + 1) (c.slotPolynomial (state i)) *
        homogeneousComponent ((rightDegree d b).val + 1) (c.slotPolynomial (state j)) := by
  classical
  let prod (s : Fin d.val × H × H) : MvPolynomial V R :=
    homogeneousComponent ((leftDegree d s.1).val + 1) (c.slotPolynomial (state s.2.1)) *
    homogeneousComponent ((rightDegree d s.1).val + 1) (c.slotPolynomial (state s.2.2))
  have hmem : homogeneousComponent (d.val + 1) (c.slotPolynomial (state h)) ∈
      Submodule.span R (Set.range prod) := by
    apply c.slot_component_mem (by omega)
    intro i j a b ha hb hab
    obtain ⟨i', rfl⟩ := surj i
    obtain ⟨j', rfl⟩ := surj j
    let split : Fin d.val := ⟨a - 1, by omega⟩
    have hl : (leftDegree d split).val + 1 = a := by change a - 1 + 1 = a; omega
    have hr : (rightDegree d split).val + 1 = b := by
      have htotal := split_degrees d split
      omega
    rw [← hl, ← hr]
    exact Submodule.subset_span (Set.mem_range_self (split, i', j') : prod _ ∈ _)
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hmem
  refine ⟨fun b i j ↦ w (b, i, j), ?_⟩
  simpa only [Fintype.sum_prod_type, prod, smul_eq_C_mul, mul_assoc] using hw.symm

/-- A single assignment of the scalar labels represents the given circuit at every
state and every degree up to `D`. The state list can contain extra copies of any slot. -/
theorem Circuit.exists_parseGrammar_on (c : Circuit R V n) (D : ℕ)
    (state : H → Circuit.GrammarSlots V n) (surj : Function.Surjective state) :
    ∃ G : ParseGrammar R V H D, ∀ d h,
      G.eval d h = homogeneousComponent (d.val + 1) (c.slotPolynomial (state h)) := by
  classical
  let binary (d : Fin D) (h : H) : Fin d.val → H → H → R :=
    if hd : d.val ≠ 0 then (c.exists_production_labels state surj d h hd).choose
    else fun _ _ _ ↦ 0
  let G : ParseGrammar R V H D :=
    ⟨fun h v ↦ (c.slotPolynomial (state h)).coeff (Finsupp.single v 1), binary⟩
  refine ⟨G, G.eval_eq_of_recurrence _ ?_ ?_⟩
  · intro d h hd
    simpa only [hd, zero_add] using homogeneousComponent_one_eq_sum (c.slotPolynomial (state h))
  · intro d h hd
    simpa only [G, binary, dite_eq_left hd] using
      (c.exists_production_labels state surj d h hd).choose_spec

/-- The start state computes the requested piece of the exact output polynomial. -/
theorem Circuit.exists_parseGrammar (c : Circuit R V n) (D : ℕ) :
    ∃ G : ParseGrammar R V (Circuit.GrammarSlots V n) D, ∀ d,
      G.eval d none = homogeneousComponent (d.val + 1) c.polynomial := by
  obtain ⟨G, hG⟩ := c.exists_parseGrammar_on D id Function.surjective_id
  exact ⟨G, fun d ↦ hG d none⟩

/-- The state count is one plus the number of variables and binary gates. -/
theorem Circuit.card_grammarSlots (V : Type*) [Fintype V] (n : ℕ) :
    Fintype.card (Circuit.GrammarSlots V n) = Fintype.card V + n + 1 := by
  simp [GrammarSlots]

/-- The prescribed rectangular table can be padded to any sufficiently large width.
The start slot is number zero (number one in the paper). -/
theorem Circuit.exists_parseGrammar_fin (c : Circuit R V n) (D S : ℕ)
    (hS : Fintype.card V + n + 1 ≤ S) :
    ∃ G : ParseGrammar R V (Fin S) D, ∀ d,
      G.eval d ⟨0, by omega⟩ = homogeneousComponent (d.val + 1) c.polynomial := by
  classical
  obtain ⟨e⟩ : Nonempty (Circuit.GrammarSlots V n ↪ Fin S) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [card_grammarSlots, Fintype.card_fin])
  let start : Fin S := ⟨0, by omega⟩
  let switch := Equiv.swap (e none) start
  let state : Fin S → Circuit.GrammarSlots V n := Function.invFun e ∘ switch
  have hs : Function.Surjective state :=
    (Function.leftInverse_invFun e.injective).surjective.comp switch.surjective
  obtain ⟨G, hG⟩ := c.exists_parseGrammar_on D state hs
  have hstart : state start = none := by
    simp only [state, switch, Function.comp_apply, Equiv.swap_apply_right]
    exact Function.leftInverse_invFun e.injective none
  exact ⟨G, fun d ↦ by simpa only [hstart, slotPolynomial] using hG d start⟩

end VPVNP
end Computability
end OAI
