import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.ChoiceTable
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-! # A choice table for the signed CNF verifier

A variable block stores its assignment bit. A clause block identifies its
first satisfied literal, which gives exactly one compatible choice for each
satisfying assignment, even for clauses with repeated literals.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
namespace CompanionCNF

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph
open scoped Classical BigOperators

variable {k m : ℕ} {R σ : Type*} [CommRing R]
private abbrev Block (k m : ℕ) := Fin k ⊕ Fin m
private abbrev Clauses (k m : ℕ) := Fin m → List (Fin k × Bool)

private def Entry (cl : Clauses k m) : Block k m → Type
  | .inl _ => Bool
  | .inr j => Fin (cl j).length

private instance (cl : Clauses k m) (i : Block k m) : Fintype (Entry cl i) := by
  cases i <;> unfold Entry <;> infer_instance

private def Agrees (c : List (Fin k × Bool)) (p : Fin c.length) (i : Fin k) (b : Bool) : Prop :=
  (i = (c.get p).1 → b = (c.get p).2) ∧
    ∀ t : Fin c.length, t < p → i = (c.get t).1 → b ≠ (c.get t).2

private def conflict (cl : Clauses k m) :
    (u v : Block k m) → Entry cl u → Entry cl v → Prop
  | .inr j, .inl i, p, b => ¬Agrees (cl j) p i b
  | _, _, _, _ => False

private def weight (cl : Clauses k m) (w : Fin k → ProjectionAtom R σ) :
    (u : Block k m) → Entry cl u → ProjectionAtom R σ
  | .inl i, b => if b = true then w i else .inr 1
  | .inr _, _ => .inr 1

/-- One row per variable and clause, with the signs or variables attached to true bits. -/
def table (cl : Fin m → List (Fin k × Bool)) (w : Fin k → ProjectionAtom R σ) : ChoiceTable R σ where
  Block := Block k m
  Option := Entry cl
  conflict := fun a b => conflict cl a.1 b.1 a.2 b.2
  w := fun a => weight cl w a.1 a.2

private def First (c : List (Fin k × Bool)) (x : Fin k → Bool) (p : Fin c.length) : Prop :=
  x (c.get p).1 = (c.get p).2 ∧ ∀ t < p, x (c.get t).1 ≠ (c.get t).2

private theorem compatible_iff (cl : Clauses k m) (w : Fin k → ProjectionAtom R σ)
    (s : ∀ u, Entry cl u) :
    compatibleSelector (table cl w).conflict s ↔
      ∀ j, First (cl j) (fun i => s (.inl i)) (s (.inr j)) := by
  constructor
  · intro hs j
    have h (i : Fin k) : Agrees (cl j) (s (.inr j)) i (s (.inl i)) :=
      not_not.mp (hs (.inr j) (.inl i) Sum.inr_ne_inl)
    exact ⟨(h _).1 rfl, fun t ht => (h _).2 t ht rfl⟩
  · intro h a b _
    cases a with
    | inl i => cases b <;> simp [table,conflict]
    | inr j =>
      cases b with
      | inr l => simp [table,conflict]
      | inl i =>
        apply not_not.mpr
        exact ⟨fun e => e ▸ (h j).1, fun t ht e => e ▸ (h j).2 t ht⟩

private theorem exists_unique_first (c : List (Fin k × Bool)) (x : Fin k → Bool)
    (h : ∃ p : Fin c.length, x (c.get p).1 = (c.get p).2) : ∃! p, First c x p := by
  classical
  let hits := Finset.univ.filter fun p : Fin c.length => x (c.get p).1 = (c.get p).2
  have non : hits.Nonempty := h.imp fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
  let p := hits.min' non
  have hp : p ∈ hits := hits.min'_mem non
  refine ⟨p, ⟨(Finset.mem_filter.mp hp).2,fun t ht hit =>
    (not_lt_of_ge (hits.min'_le t (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩))) ht⟩,?_⟩
  intro t ht
  apply le_antisymm _ (hits.min'_le t (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht.1⟩))
  exact le_of_not_gt fun hlt => ht.2 p hlt (Finset.mem_filter.mp hp).2

/-- Summing all table rows counts each satisfying assignment with its prescribed weight. -/
theorem table_polynomial (cl : Fin m → List (Fin k × Bool)) (w : Fin k → ProjectionAtom R σ) :
    (table cl w).polynomial = ∑ x : Fin k → Bool,
      if ∀ j, ∃ t : Fin (cl j).length, x ((cl j).get t).1 = ((cl j).get t).2
      then ∏ i, if x i then atomPolynomial (w i) else 1 else 0 := by
  classical
  let I := fun j : Fin m => Fin (cl j).length
  let term (z : (Fin k → Bool) × (∀ j, I j)) : MvPolynomial σ R :=
    if ∀ j, First (cl j) z.1 (z.2 j) then ∏ i, if z.1 i then atomPolynomial (w i) else 1 else 0
  calc
    _ = ∑ z, term z := by
      unfold ChoiceTable.polynomial
      let : DecidableEq (Block k m) := fun a b => Classical.propDecidable (a = b)
      apply Fintype.sum_equiv (Equiv.sumPiEquivProdPi (Entry cl)) _ _
      intro s
      rw [compatible_iff]
      dsimp only [term,Equiv.sumPiEquivProdPi,Equiv.coe_fn_mk]
      congr 1
      change (∏ b : Fin k ⊕ Fin m, atomPolynomial (weight cl w b (s b))) = _
      rw [Fintype.prod_sum_type]
      have unit (j : Fin m) : atomPolynomial (weight cl w (.inr j) (s (.inr j))) = 1 :=
        MvPolynomial.C_1
      simp only [unit, Finset.prod_const_one, mul_one]
      apply Finset.prod_congr rfl
      intro i _
      change atomPolynomial (if s (.inl i) = true then w i else .inr 1) = _
      split <;> simp_all [atomPolynomial]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      by_cases good : ∀ j, ∃ t : Fin (cl j).length, x ((cl j).get t).1 = ((cl j).get t).2
      · rw [ite_eq_left good]
        choose y hy unique using fun j => exists_unique_first (cl j) x (good j)
        rw [Finset.sum_eq_single y]
        · exact ite_eq_left hy
        · intro b _ hb
          apply ite_eq_right
          exact fun h => hb (funext fun j => unique j _ (h j))
        · simp
      · rw [ite_eq_right good]
        apply Finset.sum_eq_zero
        intro b _
        apply ite_eq_right
        exact fun h => good (fun j => ⟨b j, (h j).1⟩)

/-- A linear bound in the number of variables, clauses and available literal positions. -/
theorem table_size_le (cl : Fin m → List (Fin k × Bool)) (w : Fin k → ProjectionAtom R σ)
    {L : ℕ} (bounded : ∀ j, (cl j).length ≤ L) : (table cl w).size ≤ 3*k+m*(L+1) := by
  change Fintype.card (Fin k ⊕ Fin m) + Fintype.card (Sigma (Entry cl)) ≤ _
  rw [Fintype.card_sigma]
  change _ + (∑ i : Fin k ⊕ Fin m, Fintype.card (Entry cl i)) ≤ _
  simp only [Fintype.card_sum, Fintype.card_fin,Fintype.sum_sum_type,Entry,Fintype.card_bool,
    Finset.sum_const,Finset.card_univ,smul_eq_mul]
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => bounded i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  rw [Nat.mul_add, Nat.mul_one]
  omega

private theorem satisfies_iff_positions (cs : List (List (Fin k × Bool))) (x : Fin k → Bool) :
    (∀ j : Fin cs.length, ∃ t : Fin (cs.get j).length,
      x ((cs.get j).get t).1 = ((cs.get j).get t).2) ↔
      ∀ c ∈ cs, ∃ lit ∈ c, x lit.1 = lit.2 := by
  constructor
  · intro h c hc
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hc
    obtain ⟨t,ht⟩ := h j
    exact ⟨_, List.get_mem _ t, ht⟩
  · intro h j
    obtain ⟨u,hu,hit⟩ := h _ (cs.get_mem j)
    obtain ⟨t,rfl⟩ := List.mem_iff_get.mp hu
    exact ⟨t,hit⟩

/-- Base change of the integer signed assignment sum uses the same table when
every true-variable weight is a coefficient or a single variable. -/
theorem table_integer (cs : List (List (Fin k × Bool))) (w : Fin k → ProjectionAtom R σ)
    (integer : Fin k → MvPolynomial σ ℤ)
    (weights : ∀ i, atomPolynomial (w i) = MvPolynomial.map (Int.castRingHom R) (integer i)) :
    (table cs.get w).polynomial = MvPolynomial.map (Int.castRingHom R)
      (∑ x : Fin k → Bool, if ∀ c ∈ cs, ∃ lit ∈ c, x lit.1 = lit.2
        then ∏ i, if x i then integer i else 1 else 0) := by
  classical
  rw [table_polynomial,map_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hit : ∀ c ∈ cs, ∃ lit ∈ c, x lit.1 = lit.2
  · simp only [ite_eq_left ((satisfies_iff_positions cs x).mpr hit),ite_eq_left hit,map_prod]
    apply Finset.prod_congr rfl
    intro i _
    cases x i <;> simp [weights]
  · simp only [ite_eq_right (mt (satisfies_iff_positions cs x).mp hit),ite_eq_right hit,map_zero]

theorem table_list_size_le (cs : List (List (Fin k × Bool))) (w : Fin k → ProjectionAtom R σ) :
    (table cs.get w).size ≤ 3*k + cs.length*((cs.map List.length).sum+1) :=
  table_size_le _ _ (fun j => List.le_sum_of_mem (List.mem_map_of_mem (cs.get_mem j)))

end CompanionCNF

end

end FiniteFourier
end LinearAlgebra
end OAI
