import OAI.Computability.VPVNP.MatchClauses
import OAI.Computability.VPVNP.HardnessWeights

/-! # Weighted literal encoding of a tensor power

The input gives one sequence of binary digits per party. Word flags select
one variable at each party and digit-tuple flags select one coefficient per
copy of the tensor. The CNF has exactly one satisfying extension of each input.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TensorPowerCNF

open HardnessCNF MvPolynomial
open scoped Classical

/-- A block of `b` bits selecting a local basis index in one tensor factor. -/
abbrev Digit (b : ℕ) := Fin b → Bool
/-- The `h` successive local index blocks selected by one party in the tensor power. -/
abbrev Word (b h : ℕ) := Fin h → Digit b

/-- The multilinear form of the tensor power, grouping copies at each party. -/
noncomputable def form {J R : Type*} [Fintype J] [CommSemiring R] {b : ℕ}
    (T : (J → Digit b) → R) (h : ℕ) : MvPolynomial (J × Word b h) R :=
  ∑ x : J → Word b h, (∏ j, X (j, x j)) * ∏ t, C (T (fun j => x j t))

private abbrev Coordinates (J : Type*) (b h : ℕ) :=
  (J × (Fin h × Fin b)) ⊕ (J × Word b h) ⊕ (Fin h × (J → Digit b))

/-- Number of bits including the two families of flags. -/
noncomputable def width (J : Type*) [Fintype J] (b h : ℕ) :=
  Fintype.card (Coordinates J b h)

theorem width_eq (J : Type*) [Fintype J] (b h : ℕ) :
    width J b h = Fintype.card J * (h * b) + Fintype.card J * (2 ^ b) ^ h +
      h * (2 ^ b) ^ Fintype.card J := by
  simp [width, Coordinates, Word, Digit, add_assoc]

variable {J : Type*} [Fintype J] {b h : ℕ}

private noncomputable abbrev index : Coordinates J b h ≃ Fin (width J b h) :=
  Fintype.equivFin _

private noncomputable def bit (j : J) (t : Fin h) (a : Fin b) : Fin (width J b h) :=
  index (.inl (j, t, a))

private noncomputable def wordFlag (j : J) (w : Word b h) : Fin (width J b h) :=
  index (.inr (.inl (j, w)))

private noncomputable def tupleFlag (t : Fin h) (u : J → Digit b) : Fin (width J b h) :=
  index (.inr (.inr (t, u)))

private noncomputable def wordClauses (p : J × Word b h) : CNF (width J b h) :=
  matchClauses (wordFlag p.1 p.2) (fun z : Fin h × Fin b => bit p.1 z.1 z.2)
    (fun z => p.2 z.1 z.2)

private noncomputable def tupleClauses (p : Fin h × (J → Digit b)) : CNF (width J b h) :=
  matchClauses (tupleFlag p.1 p.2) (fun z : J × Fin b => bit z.1 p.1 z.2)
    (fun z => p.2 z.1 z.2)

/-- All word and tuple match tests. -/
noncomputable def formula (J : Type*) [Fintype J] (b h : ℕ) : CNF (width J b h) :=
  meetCNF wordClauses ++ meetCNF tupleClauses

theorem literalCount_formula (J : Type*) [Fintype J] (b h : ℕ) :
    literalCount (formula J b h) = Fintype.card J * (2 ^ b) ^ h * (3 * (h * b) + 1) +
      h * (2 ^ b) ^ Fintype.card J * (3 * (Fintype.card J * b) + 1) := by
  have hcount {k : ℕ} (a c : CNF k) :
      literalCount (a ++ c) = literalCount a + literalCount c := by simp [literalCount]
  rw [formula, hcount, literalCount_meetCNF_const wordClauses (3 * (h*b) + 1),
    literalCount_meetCNF_const tupleClauses (3 * (Fintype.card J * b) + 1)]
  · simp [Word, Digit]
  · intro i
    simp [tupleClauses, literalCount_matchClauses]
  · intro i
    simp [wordClauses, literalCount_matchClauses]

private noncomputable def bits (v : Fin (width J b h) → Bool) : J → Word b h :=
  fun j t a => v (bit j t a)

private theorem satisfies_iff (v : Fin (width J b h) → Bool) :
    Satisfies (formula J b h) v ↔
      (∀ j w, v (wordFlag j w) = true ↔ bits v j = w) ∧
      (∀ t u, v (tupleFlag t u) = true ↔ (fun j => bits v j t) = u) := by
  have happ {k : ℕ} (a c : CNF k) (x : Fin k → Bool) :
      Satisfies (a ++ c) x ↔ Satisfies a x ∧ Satisfies c x := by
    simp [Satisfies]
    aesop
  simp only [formula, happ, satisfies_meetCNF, wordClauses, tupleClauses, satisfies_matchClauses,
    Prod.forall, funext_iff, bits]

private noncomputable def extendAt (x : J → Word b h) : Coordinates J b h → Bool
  | .inl (j, t, a) => x j t a
  | .inr (.inl (j, w)) => decide (x j = w)
  | .inr (.inr (t, u)) => decide ((fun j => x j t) = u)

private noncomputable def extend (x : J → Word b h) : Fin (width J b h) → Bool :=
  extendAt x ∘ index.symm

@[simp] private theorem extend_index (x : J → Word b h) (i : Coordinates J b h) :
    extend x (index i) = extendAt x i := by simp [extend]

@[simp] private theorem bits_extend (x : J → Word b h) : bits (extend x) = x := by
  funext j t a
  simp [bits, bit, extendAt]

private theorem satisfies_extend (x : J → Word b h) : Satisfies (formula J b h) (extend x) := by
  simp [satisfies_iff, wordFlag, tupleFlag, extendAt]

private noncomputable def satisfyingEquiv :
    (J → Word b h) ≃ {v // Satisfies (formula J b h) v} where
  toFun x := ⟨extend x, satisfies_extend x⟩
  invFun v := bits v.val
  left_inv := bits_extend
  right_inv v := by
    apply Subtype.ext
    funext i
    obtain ⟨c, rfl⟩ := index.surjective i
    change extend (bits v.val) (index c) = v.val (index c)
    rw [extend_index]
    obtain ⟨hw, ht⟩ := (satisfies_iff v.val).mp v.property
    rcases c with ⟨j,t,a⟩ | (⟨j,w⟩ | ⟨t,u⟩)
    · rfl
    · change decide (bits v.val j = w) = v.val (wordFlag j w)
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using (hw j w).symm
    · change decide ((fun j => bits v.val j t) = u) = v.val (tupleFlag t u)
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using (ht t u).symm

variable {R : Type*} [CommSemiring R]

private def weightAt (T : (J → Digit b) → R) : Coordinates J b h → (J × Word b h) ⊕ R
  | .inl _ => .inr 1
  | .inr (.inl p) => .inl p
  | .inr (.inr (_, u)) => .inr (T u)

/-- Each bit weight is either a scalar or one variable. -/
noncomputable def weights (T : (J → Digit b) → R) (h : ℕ) :
    Fin (width J b h) → (J × Word b h) ⊕ R := weightAt T ∘ index.symm

private theorem extension_weight (T : (J → Digit b) → R) (x : J → Word b h) :
    (∏ i, if extend x i then (weights T h i).elim X C else 1) =
      (∏ j, X (j, x j)) * ∏ t, C (T (fun j => x j t)) := by
  rw [← index.prod_comp (fun i => if extend x i then (weights T h i).elim X C else 1)]
  simp only [extend_index, weights, Function.comp_apply, Equiv.symm_apply_apply,
    Fintype.prod_sum_type, Fintype.prod_prod_type, extendAt, weightAt, Sum.elim_inr,
    Sum.elim_inl, map_one, ite_self, Finset.prod_const_one, one_mul, decide_eq_true_eq]
  simp

/-- The weighted satisfying-assignment polynomial is exactly the tensor power form. -/
theorem weightedCNF_formula (T : (J → Digit b) → R) (h : ℕ) :
    weightedCNF (formula J b h) (fun i => (weights T h i).elim X C) = form T h := by
  have hs {k : ℕ} (f : CNF k) (w : Fin k → MvPolynomial (J × Word b h) R) :
      weightedCNF f w = ∑ v : {x // Satisfies f x}, ∏ i, if v.val i then w i else 1 := by
    rw [weightedCNF, ← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun x => by simp) _
  rw [hs, ← satisfyingEquiv.sum_comp, form]
  exact Finset.sum_congr rfl (fun x _ => extension_weight T x)

end TensorPowerCNF

end VPVNP
end Computability
end OAI
