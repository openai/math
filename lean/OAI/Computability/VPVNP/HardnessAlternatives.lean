import OAI.Computability.VPVNP.HardnessWeights
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Choosing among weighted CNFs

Each alternative has a selector bit and a private block of data bits. The selector
bits are one-hot. The chosen formula is enforced, while every unchosen block is
filled with zeros. Consequently an accepted local assignment extends uniquely
to an accepted global assignment, even for zero-variable formulas.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HardnessAlternatives

open HardnessCNF
open scoped Classical

variable {I : Type*} [Fintype I] {k : I → ℕ}

/-- Boolean variables of the disjoint-alternatives formula. Each alternative gets a selector
and its own block of local variables. -/
abbrev Slot (k : I → ℕ) := I ⊕ (Σ i, Fin (k i))

/-- The total number of selectors and local variables in the alternatives formula. -/
def width (k : I → ℕ) := Fintype.card (Slot k)

/-- A bijection from the tagged selector and local-variable slots onto the finite set of CNF
variable indices. -/
noncomputable def index (k : I → ℕ) : Slot k ≃ Fin (width k) := Fintype.equivFin _

theorem width_le {K : ℕ} (h : ∀ i, k i ≤ K) :
    width k ≤ Fintype.card I * (1 + K) := by
  simp only [width, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, Nat.mul_add,
    Nat.mul_one]
  apply Nat.add_le_add_left
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)

private noncomputable def flag (k : I → ℕ) (i : I) := index k (.inl i)
private noncomputable def bit (k : I → ℕ) (i : I) (j : Fin (k i)) := index k (.inr ⟨i,j⟩)

private noncomputable def allIndices (I : Type*) [Fintype I] : List I :=
  (Finset.univ : Finset I).toList

@[simp] private theorem mem_allIndices (i : I) : i ∈ allIndices I := by simp [allIndices]

@[simp] private theorem length_allIndices : (allIndices I).length = Fintype.card I := by
  simp [allIndices]

private noncomputable def exclusive (k : I → ℕ) (i : I) : CNF (width k) :=
  (allIndices I).map fun j => [(flag k i, false), (flag k j, decide (i = j))]

private noncomputable def inactive (k : I → ℕ) (i : I) : CNF (width k) :=
  (List.finRange (k i)).map fun j => [(flag k i, true), (bit k i j, false)]

private noncomputable def guarded (φ : ∀ i, CNF (k i)) (i : I) : CNF (width k) :=
  if [] ∈ φ i then [[(flag k i, false)]] else
    (φ i).map fun c => (flag k i, false) :: c.map fun l => (bit k i l.1, l.2)

/-- Select exactly one formula, enforcing its clauses and zeroing all inactive variables. -/
noncomputable def formula (φ : ∀ i, CNF (k i)) : CNF (width k) :=
  ((allIndices I).map fun i => (flag k i, true)) ::
    (allIndices I).flatMap fun i => exclusive k i ++ inactive k i ++ guarded φ i

private def Hits {n : ℕ} (x : Fin n → Bool) (c : List (Literal n)) : Prop :=
  ∃ l ∈ c, x l.1 = l.2

private theorem sat_map {A : Type*} {n : ℕ} (xs : List A) (f : A → List (Literal n))
    (x : Fin n → Bool) : Satisfies (xs.map f) x ↔ ∀ i ∈ xs, Hits x (f i) := by
  simp [Satisfies, Hits]

private theorem sat_append {n : ℕ} (φ ψ : CNF n) (x : Fin n → Bool) :
    Satisfies (φ ++ ψ) x ↔ Satisfies φ x ∧ Satisfies ψ x := by
  simp [Satisfies, or_imp, forall_and]

private theorem sat_exclusive (i : I) (x : Fin (width k) → Bool) :
    Satisfies (exclusive k i) x ↔ ∀ j, x (flag k i) = true → x (flag k j) = true → i = j := by
  rw [exclusive, sat_map]
  simp only [mem_allIndices, forall_const, Hits, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp]
  constructor
  · intro h j hi hj
    simpa [hi, hj] using h j
  · intro h j
    cases hi : x (flag k i) <;> cases hj : x (flag k j) <;> by_cases e : i = j <;>
      simp_all
    exact e (h j hj)

private theorem sat_inactive (i : I) (x : Fin (width k) → Bool) :
    Satisfies (inactive k i) x ↔ ∀ j, x (flag k i) = false → x (bit k i j) = false := by
  rw [inactive, sat_map]
  cases h : x (flag k i) <;> simp [Hits, h]

private theorem sat_guarded (φ : ∀ i, CNF (k i)) (i : I) (x : Fin (width k) → Bool) :
    Satisfies (guarded φ i) x ↔ x (flag k i) = true → Satisfies (φ i) (fun j => x (bit k i j)) := by
  by_cases he : [] ∈ φ i
  · have hn : ¬ Satisfies (φ i) (fun j => x (bit k i j)) := by
      intro h
      simpa using h [] he
    rw [guarded, ite_eq_left he]
    simp only [hn, imp_false]
    simp [Satisfies]
  · rw [guarded, ite_eq_right he, sat_map]
    have hit (c : List (Literal (k i))) :
        Hits x ((flag k i, false) :: c.map (fun l => (bit k i l.1, l.2))) ↔
          x (flag k i) = false ∨ Hits (fun j => x (bit k i j)) c := by
      simp only [Hits, List.mem_cons, exists_eq_or_imp, List.mem_map]
      aesop
    constructor
    · intro h hs c hc
      exact ((hit c).1 (h c hc)).resolve_left (by simp [hs])
    · intro h c hc
      apply (hit c).2
      cases hs : x (flag k i) with
      | false => exact Or.inl rfl
      | true => exact Or.inr (h hs c hc)

private theorem sat_formula (φ : ∀ i, CNF (k i)) (x : Fin (width k) → Bool) :
    Satisfies (formula φ) x ↔ (∃ i, x (flag k i) = true) ∧ ∀ i,
      (∀ j, x (flag k i) = true → x (flag k j) = true → i = j) ∧
      (∀ j, x (flag k i) = false → x (bit k i j) = false) ∧
      (x (flag k i) = true → Satisfies (φ i) (fun j => x (bit k i j))) := by
  have cons {n : ℕ} (c : List (Literal n)) (ψ : CNF n) (y : Fin n → Bool) :
      Satisfies (c :: ψ) y ↔ Hits y c ∧ Satisfies ψ y := by
    simp [Hits, Satisfies]
  have flat {n : ℕ} (l : List I) (f : I → CNF n) (y : Fin n → Bool) :
      Satisfies (l.flatMap f) y ↔ ∀ a ∈ l, Satisfies (f a) y := by
    simp [Satisfies]
    aesop
  rw [formula, cons, flat]
  simp [Hits, sat_append, sat_guarded, sat_exclusive, sat_inactive]

private noncomputable def encode (i : I) (y : Fin (k i) → Bool) : Fin (width k) → Bool :=
  fun z => ((index k).symm z).elim (fun j => decide (j = i))
    (fun s => Function.update (fun j (_ : Fin (k j)) => false) i y s.1 s.2)

@[simp] private theorem encode_flag (i j : I) (y : Fin (k i) → Bool) :
    encode i y (flag k j) = decide (j = i) := by simp [encode, flag]

@[simp] private theorem encode_bit_self (i : I) (y : Fin (k i) → Bool) (z : Fin (k i)) :
    encode i y (bit k i z) = y z := by simp [encode, bit]

private theorem encode_bit_other {i j : I} (hne : j ≠ i) (y : Fin (k i) → Bool) (z : Fin (k j)) :
    encode i y (bit k j z) = false := by simp [encode, bit, hne]

private theorem sat_encode (φ : ∀ i, CNF (k i)) (i : I) (y : Fin (k i) → Bool) :
    Satisfies (formula φ) (encode i y) ↔ Satisfies (φ i) y := by
  rw [sat_formula]
  constructor
  · rintro ⟨_, h⟩
    simpa using (h i).2.2 (by simp)
  · intro h
    refine ⟨⟨i, by simp⟩, fun j => ⟨?_, ?_, ?_⟩⟩
    · simp +contextual
    · intro z hj
      exact encode_bit_other (by simpa using hj) _ _
    · intro hj
      have : j = i := by simpa using hj
      subst j
      simpa using h

private noncomputable def solutions (φ : ∀ i, CNF (k i)) :
    (Σ i, {y : Fin (k i) → Bool // Satisfies (φ i) y}) ≃
      {x : Fin (width k) → Bool // Satisfies (formula φ) x} := by
  let f : (Σ i, {y : Fin (k i) → Bool // Satisfies (φ i) y}) →
      {x : Fin (width k) → Bool // Satisfies (formula φ) x} :=
    fun ⟨i,y⟩ => ⟨encode i y.val, (sat_encode φ i y.val).2 y.property⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨i,y⟩ ⟨j,z⟩ he
    have h : encode i y.val = encode j z.val := congrArg Subtype.val he
    have hij : i = j := by simpa using congrFun h (flag k i)
    subst j
    congr 1
    apply Subtype.ext
    funext u
    simpa using congrFun h (bit k i u)
  · rintro ⟨x,hx⟩
    obtain ⟨⟨i,hi⟩, hr⟩ := (sat_formula φ x).1 hx
    let y (z : Fin (k i)) := x (bit k i z)
    refine ⟨⟨i, y, (hr i).2.2 hi⟩, Subtype.ext ?_⟩
    change encode i y = x
    funext z
    obtain ⟨s,rfl⟩ := (index k).surjective z
    cases s with
    | inl j =>
      change encode i y (flag k j) = x (flag k j)
      by_cases e : j = i
      · subst j; simp [hi]
      · have hj : x (flag k j) = false := by
          cases h : x (flag k j)
          · rfl
          · exact (e ((hr j).1 i h hi)).elim
        simp [hj, e]
    | inr s =>
      obtain ⟨j,u⟩ := s
      change encode i y (bit k j u) = x (bit k j u)
      by_cases e : j = i
      · subst j; simp [y]
      · rw [encode_bit_other e]
        symm
        apply (hr j).2.1 u
        cases h : x (flag k j)
        · rfl
        · exact (e ((hr j).1 i h hi)).elim

/-- Label each selector and each data slot. The labels can be weights or any
parameters from which the weights will be built. -/
noncomputable def weight {A : Type*} (k : I → ℕ) (a : I → A) (w : ∀ i, Fin (k i) → A)
    (z : Fin (width k)) : A := ((index k).symm z).elim a (fun s => w s.1 s.2)

@[simp] theorem weight_selector {A : Type*} (k : I → ℕ) (a : I → A) (w : ∀ i, Fin (k i) → A)
    (i : I) : weight k a w (index k (.inl i)) = a i := by simp [weight]

@[simp] theorem weight_data {A : Type*} (k : I → ℕ) (a : I → A) (w : ∀ i, Fin (k i) → A)
    (i : I) (j : Fin (k i)) : weight k a w (index k (.inr ⟨i,j⟩)) = w i j := by simp [weight]

variable {R : Type*} [CommSemiring R]

private theorem prod_encode (a : I → R) (w : ∀ i, Fin (k i) → R) (i : I) (y : Fin (k i) → Bool) :
    (∏ z, if encode i y z then weight k a w z else 1) =
      a i * ∏ j, if y j then w i j else 1 := by
  rw [← (index k).prod_comp (fun z => if encode i y z then weight k a w z else 1),
    Fintype.prod_sum_type, Fintype.prod_sigma]
  have sel (j : I) : encode i y (index k (.inl j)) = decide (j = i) := encode_flag i j y
  simp only [sel, decide_eq_true_eq, weight_selector, weight_data, Finset.prod_ite_eq',
    Finset.mem_univ, ite_true]
  congr 1
  rw [Finset.prod_eq_single i]
  · have self (j : Fin (k i)) : encode i y (index k (.inr ⟨i,j⟩)) = y j :=
      encode_bit_self i y j
    simp [self]
  · intro j _ hj
    have other (z : Fin (k j)) : encode i y (index k (.inr ⟨j,z⟩)) = false :=
      encode_bit_other hj y z
    simp [other]
  · simp

private theorem weightedCNF_eq_sum_subtype {n : ℕ} (φ : CNF n) (w : Fin n → R) :
    weightedCNF φ w = ∑ x : {x : Fin n → Bool // Satisfies φ x},
      ∏ j, if x.val j then w j else 1 := by
  rw [weightedCNF, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- The polynomial of the selector formula is the sum of the individual polynomials,
each multiplied by the weight of its selected branch. -/
theorem weighted_formula (φ : ∀ i, CNF (k i)) (a : I → R) (w : ∀ i, Fin (k i) → R) :
    weightedCNF (formula φ) (weight k a w) = ∑ i, a i * weightedCNF (φ i) (w i) := by
  simp only [weightedCNF_eq_sum_subtype, Finset.mul_sum]
  rw [← (solutions φ).sum_comp (fun x => ∏ j, if x.val j then weight k a w j else 1),
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl fun x _ => prod_encode a w i x.val

private theorem literalCount_append {n : ℕ} (a b : CNF n) :
    literalCount (a ++ b) = literalCount a + literalCount b := by simp [literalCount]

private theorem literalCount_flatMap_le {n : ℕ} {A : Type*} (xs : List A) (f : A → CNF n)
    (M : ℕ) (h : ∀ i, literalCount (f i) ≤ M) :
    literalCount (xs.flatMap f) ≤ xs.length * M := by
  induction xs with
  | nil => simp [literalCount]
  | cons a xs ih =>
    simpa [literalCount_append, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add (h a) ih

private theorem literalCount_guarded_le (φ : ∀ i, CNF (k i)) (i : I) :
    literalCount (guarded φ i) ≤ 1 + 2 * literalCount (φ i) := by
  by_cases he : [] ∈ φ i
  · simp [guarded, he, literalCount]
  · rw [guarded, ite_eq_right he]
    generalize hv : φ i = cs at *
    clear hv
    induction cs with
    | nil => simp [literalCount]
    | cons c cs ih =>
      have hn : c ≠ [] := by aesop
      have hp : 0 < c.length := List.length_pos_iff.mpr hn
      have htail := ih (by aesop)
      simp only [List.map_cons, literalCount, List.sum_cons, List.length_map, List.length_cons]
      simp only [literalCount] at htail
      omega

private theorem literalCount_map_const {A : Type*} {n : ℕ} (xs : List A) (f : A → List (Literal n))
    (v : ℕ) (hv : ∀ a, (f a).length = v) :
    literalCount (xs.map f) = xs.length * v := by
  induction xs with
  | nil => simp [literalCount]
  | cons x xs ih => simpa [literalCount, hv, Nat.succ_mul, Nat.add_comm] using ih

/-- A uniform bound in the number of alternatives, the largest block width,
and the largest literal count. Empty clauses are detected before guarding. -/
theorem literalCount_formula_le (φ : ∀ i, CNF (k i)) {K L : ℕ}
    (hk : ∀ i, k i ≤ K) (hl : ∀ i, literalCount (φ i) ≤ L) :
    literalCount (formula φ) ≤ Fintype.card I +
      Fintype.card I * (2 * Fintype.card I + 2 * K + 1 + 2 * L) := by
  rw [formula]
  change ((allIndices I).map fun i => (flag k i, true)).length + literalCount _ ≤ _
  simp only [List.length_map, length_allIndices]
  apply Nat.add_le_add_left
  refine (literalCount_flatMap_le (allIndices I) _
    (2 * Fintype.card I + 2 * K + 1 + 2 * L) ?_).trans_eq (by simp)
  intro i
  have he : literalCount (exclusive k i) = Fintype.card I * 2 := by
    rw [exclusive, literalCount_map_const (v := 2) (hv := fun _ => rfl), length_allIndices]
  have ha : literalCount (inactive k i) = k i * 2 := by
    rw [inactive, literalCount_map_const (v := 2) (hv := fun _ => rfl), List.length_finRange]
  simp only [literalCount_append, he, ha]
  have := literalCount_guarded_le φ i
  have := hk i
  have := hl i
  omega

end HardnessAlternatives

end VPVNP
end Computability
end OAI
