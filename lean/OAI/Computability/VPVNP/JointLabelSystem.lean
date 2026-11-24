import OAI.Computability.VPVNP.GrammarAssignment
import OAI.Computability.VPVNP.GrammarSize
import OAI.Computability.VPVNP.PolynomialBounds
import OAI.Computability.VPVNP.MotifParameters

/-!
# The joint integer label equations of Section 8.1

The grammar labels and the entries of the fixed motif maps are disjoint sets
of variables. Enumerating their union gives one finite list of variables for
the field-descent and Macaulay constructions. Every solution specializes the
two systems simultaneously, over any commutative coefficient ring.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointLabelSystem

open MvPolynomial

variable {V W I J : Type*} [Fintype V] [Fintype W]

/-- Index of a variable from the first system in the joint coordinate list. -/
noncomputable def leftIndex (V W : Type*) [Fintype V] [Fintype W] :
    V ↪ Fin (Fintype.card (V ⊕ W)) :=
  ⟨fun v => Fintype.equivFin (V ⊕ W) (.inl v), (Fintype.equivFin _).injective.comp Sum.inl_injective⟩

/-- Index of a variable from the second system in the joint coordinate list. -/
noncomputable def rightIndex (V W : Type*) [Fintype V] [Fintype W] :
    W ↪ Fin (Fintype.card (V ⊕ W)) :=
  ⟨fun w => Fintype.equivFin (V ⊕ W) (.inr w), (Fintype.equivFin _).injective.comp Sum.inr_injective⟩

/-- Place the two lists of integer equations in one ring on numbered variables. -/
noncomputable def unionEquations (F : I → MvPolynomial V ℤ) (G : J → MvPolynomial W ℤ) :
    I ⊕ J → MvPolynomial (Fin (Fintype.card (V ⊕ W))) ℤ :=
  Sum.elim (fun i => rename (leftIndex V W) (F i)) (fun j => rename (rightIndex V W) (G j))

/-- Pulling a joint assignment back along the two coordinate embeddings yields
exactly the simultaneous solutions of the original systems. -/
theorem unionEquations_solution_iff {R : Type*} [CommRing R] (F : I → MvPolynomial V ℤ)
    (G : J → MvPolynomial W ℤ) (a : Fin (Fintype.card (V ⊕ W)) → R) :
    (∀ j, eval₂Hom (Int.castRingHom R) a (unionEquations F G j) = 0) ↔
      (∀ i, eval₂Hom (Int.castRingHom R) (a ∘ leftIndex V W) (F i) = 0) ∧
      (∀ j, eval₂Hom (Int.castRingHom R) (a ∘ rightIndex V W) (G j) = 0) := by
  simp only [Sum.forall, unionEquations, Sum.elim_inl, Sum.elim_inr, eval₂Hom_rename]

/-- Combine two label assignments into the common list of numbered coordinates. -/
noncomputable def joinAssignment {R : Type*} (a : V → R) (b : W → R) :
    Fin (Fintype.card (V ⊕ W)) → R :=
  Sum.elim a b ∘ (Fintype.equivFin (V ⊕ W)).symm

@[simp] theorem joinAssignment_left {R : Type*} (a : V → R) (b : W → R) :
    joinAssignment a b ∘ leftIndex V W = a := by
  funext v
  simp [joinAssignment, leftIndex]

@[simp] theorem joinAssignment_right {R : Type*} (a : V → R) (b : W → R) :
    joinAssignment a b ∘ rightIndex V W = b := by
  funext w
  simp [joinAssignment, rightIndex]

theorem unionEquations_totalDegree_le (F : I → MvPolynomial V ℤ) (G : J → MvPolynomial W ℤ)
    {d : ℕ} (hF : ∀ i, (F i).totalDegree ≤ d) (hG : ∀ j, (G j).totalDegree ≤ d) (j : I ⊕ J) :
    (unionEquations F G j).totalDegree ≤ d := by
  cases j with
  | inl i => exact (totalDegree_rename_le (leftIndex V W) (F i)).trans (hF i)
  | inr j => exact (totalDegree_rename_le (rightIndex V W) (G j)).trans (hG j)

private theorem coeff_natAbs_rename_le {A B : Type*} (f : A ↪ B) (p : MvPolynomial A ℤ)
    {M : ℕ} (hp : ∀ e, (p.coeff e).natAbs ≤ M) (e : B →₀ ℕ) :
    ((rename f p).coeff e).natAbs ≤ M := by
  by_cases hz : (rename f p).coeff e = 0
  · simp [hz]
  · obtain ⟨u, rfl, _⟩ := coeff_rename_ne_zero f p e hz
    rw [coeff_rename_mapDomain f f.injective]
    exact hp u

theorem unionEquations_coeff_natAbs_le (F : I → MvPolynomial V ℤ) (G : J → MvPolynomial W ℤ)
    {B : ℕ} (hF : ∀ i e, ((F i).coeff e).natAbs ≤ B)
    (hG : ∀ j e, ((G j).coeff e).natAbs ≤ B) (j : I ⊕ J)
    (e : Fin (Fintype.card (V ⊕ W)) →₀ ℕ) : ((unionEquations F G j).coeff e).natAbs ≤ B := by
  cases j with
  | inl i => exact coeff_natAbs_rename_le _ _ (hF i) _
  | inr j => exact coeff_natAbs_rename_le _ _ (hG j) _

/-- Production labels at the width used for a size `n^c` circuit. -/
abbrev Production (n c : ℕ) := GrammarLabel (Fin n × Bool) (Fin (n ^ (c + 5))) n

/-- The integer equation `Bₓ - Uₙ(x) = 0` at the designated start state. -/
noncomputable def grammarEquation {n : ℕ} (hn : 2 ≤ n) (c : ℕ) (x : Fin n → Bool) :
    MvPolynomial (Production n c) ℤ :=
  labelQuery ⟨n - 1, by omega⟩ ⟨0, pow_pos (by omega) _⟩ x - C (acceptingCount x : ℤ)

section Motif

variable {Z : Type*} [Fintype Z] [Fintype J] {n : ℕ}

/-- The full integer polynomial system for the production labels and the motif
matrix entries, in the finite coordinate format of Section 8.2. -/
noncomputable def equations (hn : 2 ≤ n) (c : ℕ) (G : MotifParameters.Data J Z) :
    (Fin n → Bool) ⊕ G.Output → MvPolynomial (Fin (Fintype.card (Production n c ⊕ G.Entry))) ℤ :=
  unionEquations (grammarEquation hn c) G.equation

/-- There is one equation per Boolean input in addition to the fixed output
coordinates of the motif data. -/
theorem equation_count [DecidableEq J] (G : MotifParameters.Data J Z) (n : ℕ) :
    Fintype.card ((Fin n → Bool) ⊕ G.Output) = 2 ^ n + Fintype.card G.Output := by
  simp

/-- The variable count of the joint system grows polynomially at each fixed
circuit exponent and fixed motif data. -/
theorem variable_count_le (G : MotifParameters.Data J Z) (n c : ℕ) :
    Fintype.card (Production n c ⊕ G.Entry) ≤
      n ^ (c + 5) * (n * 2) + n ^ 2 * (n ^ (c + 5)) ^ 3 + Fintype.card G.Entry := by
  rw [Fintype.card_sum]
  apply Nat.add_le_add_right
  simpa only [Fintype.card_fin, Fintype.card_prod, Fintype.card_bool] using
    card_grammarLabel_le (Fin n × Bool) (Fin (n ^ (c + 5))) n

theorem variable_count_polynomiallyBounded (G : MotifParameters.Data J Z) (c : ℕ) :
    PolynomiallyBounded (fun n => Fintype.card (Production n c ⊕ G.Entry)) := by
  have hw := PolynomiallyBounded.id.pow (c + 5)
  exact (((hw.mul (PolynomiallyBounded.id.mul (.const 2))).add
    ((PolynomiallyBounded.id.pow 2).mul (hw.pow 3))).add (.const _)).of_le
    (fun n => variable_count_le G n c)

/-- A solution in any commutative ring gives the path counts for every input
word and specializes the integral motif identities in the same ring. -/
theorem solution_iff {R : Type*} [CommRing R] (hn : 2 ≤ n) (c : ℕ)
    (G : MotifParameters.Data J Z) (a : Fin (Fintype.card (Production n c ⊕ G.Entry)) → R) :
    (∀ j, eval₂Hom (Int.castRingHom R) a (equations hn c G j) = 0) ↔
      (∀ x : Fin n → Bool, eval₂Hom (Int.castRingHom R) (a ∘ leftIndex (Production n c) G.Entry)
        (labelQuery ⟨n - 1, by omega⟩ ⟨0, pow_pos (by omega) _⟩ x) = (acceptingCount x : R)) ∧
      G.IsSolution (a ∘ rightIndex (Production n c) G.Entry) := by
  rw [equations, unionEquations_solution_iff]
  simp [grammarEquation, MotifParameters.Data.IsSolution, sub_eq_zero]

/-- An actual small circuit and a solution of the fixed local motif equations
give a joint solution in the circuit's coefficient ring. -/
theorem exists_solution {R : Type*} [CommRing R] {c s : ℕ} (hn : 2 ≤ n) (hc : 1 ≤ c)
    (hs : s ≤ n ^ c) (circuit : Circuit R (Fin n × Bool) s)
    (hpoly : circuit.polynomial = map (Int.castRingHom R) (P n))
    (G : MotifParameters.Data J Z) (κ : G.Entry → R) (hκ : G.IsSolution κ) :
    ∃ a : Fin (Fintype.card (Production n c ⊕ G.Entry)) → R,
      ∀ j, eval₂Hom (Int.castRingHom R) a (equations hn c G j) = 0 := by
  obtain ⟨labels, hl⟩ := pathCount_labelEquations hn hc hs circuit hpoly
  refine ⟨joinAssignment labels κ, (solution_iff hn c G _).mpr ?_⟩
  simpa only [joinAssignment_left, joinAssignment_right] using And.intro hl hκ

end Motif

end JointLabelSystem

end VPVNP
end Computability
end OAI
