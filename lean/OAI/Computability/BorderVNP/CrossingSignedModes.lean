import Lemmata.FockCircuits.Families

/-!
# Signed witnesses for the fermionic modes

For a fixed derivative order, one witness selects creation or deletion and a mode.
Reading the choices in the order of the normally ordered recursion erases one mode from
the desired output (creation) or from the input (deletion). The integer weight records the
binomial coefficient and the signs of the interchanges. This gives an explicit signed
expansion of the finite operator matrices in Appendix A.

The proofs use the exterior-algebra basis and its creation and contraction operators from
Kirill Khoruzhii's Lemmata entry
[Crossing Decomposition for Subquadratic Noncommutative Circuits](https://github.com/ZIB-IOL/lemmata/blob/a2dd430f283febd755a6ee6932d0b0fdabfb330c/docs/crossing-decomposition/index.md),
licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Signed

open Lemmata.FockCircuits Lemmata.FockCircuits.FiniteIdentity
open scoped BigOperators

/-- Sign for moving the mode `k` past all earlier occupied modes. -/
def insertionSign (k : ℕ) (S : Finset ℕ) : ℤ := (-1) ^ (S.filter (· < k)).card

private theorem sign_sq (k : ℕ) (S : Finset ℕ) :
    insertionSign k S * insertionSign k S = 1 := by
  simp [insertionSign, ← mul_pow]

private theorem basis_insert_min (k : ℕ) (S : Finset ℕ) (h : ∀ j ∈ S, k < j) :
    Fock.basis ℤ (insert k S) = Fock.create ℤ k (Fock.basis ℤ S) := by
  rw [Fock.basis_eq_sorted_prod, Finset.sort_insert (· ≤ ·) (fun j hj => (h j hj).le)
    (fun hk => (h k hk).false), Fock.basis_eq_sorted_prod]
  rfl

/-- Creation on an unoccupied mode, with the explicit sign in the sorted basis. -/
theorem create_basis {k : ℕ} {S : Finset ℕ} (hk : k ∉ S) :
    Fock.create ℤ k (Fock.basis ℤ S) = insertionSign k S • Fock.basis ℤ (insert k S) := by
  induction S using Finset.induction_on_min with
  | empty => simp [insertionSign]
  | insert a S ha ih =>
    have haS : a ∉ S := fun h => (ha a h).false
    have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
    have hka : k ≠ a := fun h => hk (h ▸ Finset.mem_insert_self a S)
    by_cases h : k < a
    · have hall : ∀ j ∈ insert a S, k < j := by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact h
        · exact h.trans (ha j hj)
      have hf : (insert a S).filter (· < k) = ∅ := Finset.filter_eq_empty_iff.mpr
        (fun j hj => (hall j hj).not_gt)
      rw [basis_insert_min k _ hall]
      simp [insertionSign, hf]
    · have hak : a < k := by omega
      have hsmall : ∀ j ∈ insert k S, a < j := by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hak
        · exact ha j hj
      rw [basis_insert_min a S ha, eq_neg_of_add_eq_zero_left (Fock.create_anticommute ℤ k a _),
        ih hkS, map_smul, Finset.insert_comm k a, basis_insert_min a _ hsmall]
      simp [insertionSign, Finset.filter_insert, hak, haS, pow_succ, neg_smul]

/-- Deletion on an occupied mode has the same sign as its inverse creation. -/
theorem contract_basis {k : ℕ} {S : Finset ℕ} (hk : k ∈ S) :
    Fock.contract ℤ k (Fock.basis ℤ S) =
      insertionSign k (S.erase k) • Fock.basis ℤ (S.erase k) := by
  have h := create_basis (k := k) (S := S.erase k) (Finset.notMem_erase _ _)
  rw [Finset.insert_erase hk] at h
  have hinv : Fock.basis ℤ S =
      insertionSign k (S.erase k) • Fock.create ℤ k (Fock.basis ℤ (S.erase k)) := by
    rw [h, smul_smul, sign_sq, one_smul]
  rw [hinv, map_smul, Fock.contract_create, Fock.contract_basis_of_not_mem ℤ
    (Finset.notMem_erase k S)]
  simp

private theorem repr_create (x : Fock ℤ) (k : ℕ) (I : Finset ℕ) :
    (Fock.basis ℤ).repr (Fock.create ℤ k x) I =
      if k ∈ I then insertionSign k (I.erase k) * (Fock.basis ℤ).repr x (I.erase k) else 0 := by
  let coord (J : Finset ℕ) := (Finsupp.lapply J).comp (Fock.basis ℤ).repr.toLinearMap
  let lhs := (coord I).comp (Fock.create ℤ k)
  let rhs : Fock ℤ →ₗ[ℤ] ℤ :=
    if k ∈ I then insertionSign k (I.erase k) • coord (I.erase k) else 0
  have hr (y : Fock ℤ) : rhs y =
      if k ∈ I then insertionSign k (I.erase k) * (Fock.basis ℤ).repr y (I.erase k) else 0 := by
    by_cases hi : k ∈ I <;> simp [rhs, coord, hi]
  have h : lhs = rhs := by
    apply (Fock.basis ℤ).ext
    intro J
    change (Fock.basis ℤ).repr (Fock.create ℤ k (Fock.basis ℤ J)) I = rhs _
    rw [hr]
    by_cases hk : k ∈ J
    · have hn : J ≠ I.erase k := fun h => Finset.notMem_erase k I (h ▸ hk)
      rw [Fock.create_basis_of_mem ℤ hk, Module.Basis.repr_self_apply]
      simp [hn]
    · by_cases he : insert k J = I
      · subst I
        rw [create_basis hk, map_smul]
        simp [Finset.erase_insert hk]
      · have hn (hI : k ∈ I) : J ≠ I.erase k := fun h => he (h ▸ Finset.insert_erase hI)
        rw [create_basis hk, map_smul]
        by_cases hi : k ∈ I <;>
          simp [he, hi, hn]
  exact (LinearMap.congr_fun h x).trans (hr x)

/-- A word of `n` choices. Each choice takes one mode among `L`, with one bit for deletion. -/
def ModePath (L : ℕ) : ℕ → Type
  | 0 => Unit
  | n + 1 => (Bool × Fin L) × ModePath L n

instance instFintypeModePath (L : ℕ) (n : ℕ) : Fintype (ModePath L n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype ((Bool × Fin L) × ModePath L n))

/-- Integer weight of a particular path through a list of creation/deletion fields. -/
def modeWeight {L : ℕ} : (s : List ((Fin L → ℤ) × (Fin L → ℤ))) →
    ModePath L s.length → Finset ℕ → Finset ℕ → ℤ
  | [], _, I, J => if J = I then 1 else 0
  | a :: s, ((del, k), tail), I, J =>
    if del then
      if (k : ℕ) ∈ J then
        (-1 : ℤ) ^ s.length * a.2 k * insertionSign k (J.erase k) * modeWeight s tail I (J.erase k)
      else 0
    else
      if (k : ℕ) ∈ I then
        a.1 k * insertionSign k (I.erase k) * modeWeight s tail (I.erase k) J
      else 0

/-- The path sum equals the corresponding coefficient of the normally ordered operator. -/
theorem sum_modeWeight {L : ℕ} (s : List ((Fin L → ℤ) × (Fin L → ℤ))) (I J : Finset ℕ) :
    (Fock.basis ℤ).repr (Fock.normalList ℤ (plainList ℤ L s) (Fock.basis ℤ J)) I =
      ∑ p : ModePath L s.length, modeWeight s p I J := by
  induction s generalizing I J with
  | nil =>
    change _ = ∑ _ : Unit, if J = I then (1 : ℤ) else 0
    simp [plainList, Finsupp.single_apply]
  | cons a s ih =>
    change _ = ∑ p : (Bool × Fin L) × ModePath L s.length, _
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [plainList, List.map_cons, Fock.normalList_cons, List.length_map, createVector_finiteVector,
      contractVector_finiteVector, map_sum, map_add, map_smul, Finsupp.smul_apply,
      Finsupp.finsetSum_apply, Finsupp.add_apply, smul_eq_mul, repr_create]
    rw [add_comm, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      by_cases h : (k : ℕ) ∈ J
      · simp only [contract_basis h, map_smul, Finsupp.smul_apply, smul_eq_mul, modeWeight, h,
          ite_true, ← Finset.mul_sum, ← ih, plainList]
        ring
      · simp [Fock.contract_basis_of_not_mem ℤ h, modeWeight, h]
    · apply Finset.sum_congr rfl
      intro k _
      by_cases h : (k : ℕ) ∈ I
      · simp only [modeWeight, h, ite_true, Bool.false_eq_true, ite_false, ← Finset.mul_sum,
          ← ih, plainList]
        ring
      · simp [modeWeight, h]

/-- A pure derivative state gives the signed mode-path expansion of its matrix entry. -/
theorem matrix_single_paths {L : ℕ} (A I J : Index L) (c : ℤ) :
    matrix ℤ L (Pi.single A c) I J =
      c * ∑ p : ModePath L (sourceWord ℤ L A).length, modeWeight (sourceWord ℤ L A) p I.val J.val := by
  rw [matrix_single_eq_normalList, sum_modeWeight]

/-- The finite derivative field word with executable integer coefficient functions. -/
def derivativeWord {L : ℕ} (A : Index L) : List ((Fin L → ℤ) × (Fin L → ℤ)) :=
  A.val.sort.map fun m =>
    ((fun k => positiveCoefficient m k), (fun k => negativeCoefficient m k))

/-- The guessed normal word uses at most one mode choice per available derivative. -/
theorem derivativeWord_length_le {L : ℕ} (A : Index L) : (derivativeWord A).length ≤ L := by
  simpa [derivativeWord] using Finset.card_le_card (Finset.mem_powerset.mp A.property)

/-- The number of possible mode paths, before the integer multiplicity witness. -/
theorem card_modePath (L n : ℕ) : Fintype.card (ModePath L n) = (2 * L) ^ n := by
  induction n with
  | zero => change Fintype.card Unit = _; simp
  | succ n ih =>
    change Fintype.card ((Bool × Fin L) × ModePath L n) = _
    simp [ih, pow_succ, mul_comm]

/-- A bound on each path separately. Every recursive factor is consumed exactly once. -/
theorem modeWeight_bound {L : ℕ} (s : List ((Fin L → ℤ) × (Fin L → ℤ))) (d : ℕ)
    (hs : ∀ a ∈ s, ∀ k : Fin L, (a.1 k).natAbs ≤ 2 ^ d ∧ (a.2 k).natAbs ≤ 2 ^ d)
    (p : ModePath L s.length) (I J : Finset ℕ) :
    (modeWeight s p I J).natAbs ≤ 2 ^ (d * s.length) := by
  induction s generalizing I J with
  | nil => by_cases h : J = I <;> simp [modeWeight, h]
  | cons a s ih =>
    obtain ⟨⟨del, k⟩, tail⟩ := p
    have htail := ih (fun b hb => hs b (List.mem_cons_of_mem _ hb)) tail
    have h := hs a List.mem_cons_self k
    cases del <;> simp only [modeWeight, Bool.false_eq_true, ite_false, ite_true]
    · split_ifs with hk
      · simpa [insertionSign, Int.natAbs_mul, Int.natAbs_pow, List.length_cons,
          Nat.mul_succ, pow_add, Nat.mul_comm] using Nat.mul_le_mul h.1 (htail (I.erase k) J)
      · simp
    · split_ifs with hk
      · simpa [insertionSign, Int.natAbs_mul, Int.natAbs_pow, List.length_cons,
          Nat.mul_succ, pow_add, Nat.mul_comm] using Nat.mul_le_mul h.2 (htail I (J.erase k))
      · simp

/-- The integral multiplicity on a pure mode path has at most a quadratic number of bits. -/
theorem derivativeWeight_bound {L : ℕ} (A : Index L) (p : ModePath L (derivativeWord A).length)
    (I J : Finset ℕ) : (modeWeight (derivativeWord A) p I J).natAbs ≤ 2 ^ (2 * L * L) := by
  apply (modeWeight_bound _ (2 * L) ?_ p I J).trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (derivativeWord_length_le A)))
  intro a ha k
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp ha
  have hmem : m ∈ A.val := (Finset.mem_sort _).mp hm
  have hmL := Finset.mem_range.mp ((Finset.mem_powerset.mp A.property) hmem)
  have hkL := k.isLt
  simp only [positiveCoefficient, negativeCoefficient, Int.natAbs_natCast,
    Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul]
  exact ⟨(Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) (by omega)),
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))⟩

/-- A single bounded binary guess replaces an integer weight by signs. -/
def signedGuess (z : ℤ) (guess : ℕ) : ℤ := if guess < z.natAbs then z.sign else 0

/-- Summing the accepting signed guesses recovers the exact integer multiplicity. -/
theorem sum_signedGuess {z : ℤ} {b : ℕ} (h : z.natAbs ≤ b) :
    ∑ x ∈ Finset.range b, signedGuess z x = z := by
  rw [← Finset.sum_subset (Finset.range_mono h)]
  · calc
      _ = ∑ _ ∈ Finset.range z.natAbs, z.sign := Finset.sum_congr rfl fun x hx =>
        ite_eq_left (Finset.mem_range.mp hx)
      _ = z := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm, Int.sign_mul_natAbs]
  · intro x _ hx
    simp [signedGuess, Finset.mem_range.mpr.mt hx]

/-- Every individual guess contributes a sign or zero. -/
theorem signedGuess_values (z : ℤ) (x : ℕ) :
    signedGuess z x = -1 ∨ signedGuess z x = 0 ∨ signedGuess z x = 1 := by
  unfold signedGuess
  split_ifs
  · rcases lt_trichotomy z 0 with h | h | h
    · exact Or.inl (Int.sign_eq_neg_one_of_neg h)
    · simp [h]
    · exact Or.inr (Or.inr (Int.sign_eq_one_of_pos h))
  · simp

/-- A signed-count formula with an explicit bit budget for the multiplicity witness. -/
theorem matrix_single_signed {L : ℕ} (A I J : Index L) :
    matrix ℤ L (Pi.single A 1) I J =
      ∑ p : ModePath L (derivativeWord A).length,
        ∑ x ∈ Finset.range (2 ^ (2 * L * L)), signedGuess (modeWeight (derivativeWord A) p I.val J.val) x := by
  rw [matrix_single_paths, one_mul]
  apply Finset.sum_congr rfl
  intro p _
  exact (sum_signedGuess (derivativeWeight_bound A p I.val J.val)).symm

end Crossing.Signed

end BorderVNP
end Computability
end OAI
