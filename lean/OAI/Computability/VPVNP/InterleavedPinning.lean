import OAI.Computability.VPVNP.HardnessQuery
import Mathlib.Data.List.FinRange

/-!
# Projections with interleaved fixed and free input bits

A deterministic input format may place prescribed bits among the bits that
carry weights. Fixing the prescribed coordinates retains exactly the paired
monomials indexed by fillings of the free coordinates.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace InterleavedPinning

open MvPolynomial

variable {n k : ℕ} {R V : Type*} [CommRing R]

/-- Fill the free positions of an input, preserving its prescribed bits. -/
def fill (layout : Fin n → Bool ⊕ Fin k) (x : Fin k → Bool) (i : Fin n) : Bool :=
  (layout i).elim id x

private def pin (layout : Fin n → Bool ⊕ Fin k) (weight : Projection R (Fin k) V) :
    Projection R (Fin n × Bool) V := fun (i, v) =>
  match layout i with
  | .inl b => .inr (if v = b then 1 else 0)
  | .inr j => if v then weight j else .inr 1

/-- The source index is fixed in advance. Only accepting counts on the specified
fillings enter the weighted predicate. -/
theorem weighted_projection (layout : Fin n → Bool ⊕ Fin k)
    (hu : ∀ j, ∃! i, layout i = .inr j)
    (p : (Fin k → Bool) → Bool) (weight : Projection R (Fin k) V)
    (hcount : ∀ x, acceptingCount (fill layout x) = (p x).toNat) :
    ∃ φ : Projection R (Fin n × Bool) V,
      φ.hom (MvPolynomial.map (Int.castRingHom R) (P n)) = weightedPredicate p weight := by
  classical
  choose slot hs huniq using hu
  have slot_inj : Function.Injective slot := by
    intro a b hab
    exact Sum.inr.inj ((hs a).symm.trans ((congrArg layout hab).trans (hs b)))
  have fill_inj : Function.Injective (fill layout) := by
    intro x y he
    funext j
    simpa [fill, hs] using congrFun he (slot j)
  let factor (w : Fin n → Bool) (i : Fin n) : MvPolynomial V R :=
    (pin layout weight (i, w i)).elim X C
  have hprod (x : Fin k → Bool) : (∏ i, factor (fill layout x) i) =
      ∏ j, if x j then (weight j).elim X C else 1 := by
    rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image slot)),
      Finset.prod_image slot_inj.injOn]
    · apply Finset.prod_congr rfl
      intro j _
      cases hj : x j <;> simp [factor, pin, fill, hs, hj]
    · intro i _ hi
      cases hl : layout i with
      | inl b => simp [factor, pin, fill, hl]
      | inr j => exact (hi (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, (huniq j i hl).symm⟩)).elim
  have hzero (w : Fin n → Bool) (hw : w ∉ Finset.univ.image (fill layout)) :
      (∏ i, factor w i) = 0 := by
    have hbad : ∃ i b, layout i = .inl b ∧ w i ≠ b := by
      by_contra! h
      apply hw
      refine Finset.mem_image.mpr ⟨w ∘ slot, Finset.mem_univ _, ?_⟩
      funext i
      cases hl : layout i with
      | inl b => simp [fill, hl, h i b hl]
      | inr j => simp [fill, huniq j i hl, hs]
    obtain ⟨i, b, hl, hne⟩ := hbad
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [factor, pin, hl, hne])
  refine ⟨pin layout weight, ?_⟩
  rw [map_P]
  simp only [Projection.hom, pairedPolynomial, map_sum, map_mul, eval₂Hom_C, map_prod,
    eval₂Hom_X']
  change (∑ w, C (acceptingCount w : R) * ∏ i, factor w i) = _
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (fill layout))),
    Finset.sum_image fill_inj.injOn, weightedPredicate]
  · apply Finset.sum_congr rfl
    intro x _
    rw [hprod, hcount]
    cases hp : p x <;> simp
  · intro w _ hw
    simp [hzero w hw]

/-- A column record has a marker, one free bit, and its list of prescribed flags.
The machine scans these records from the right end of the physical input. -/
def recordLayout (padded : List Bool) (flags : Fin k → List Bool) : List (Bool ⊕ Fin k) :=
  padded.map Sum.inl ++
    ((List.finRange k).flatMap (fun i => Sum.inl true :: Sum.inr i :: (flags i).map Sum.inl) ++
      [Sum.inl false]).reverse

/-- The physical input obtained by filling all column records. -/
theorem recordLayout_fill (padded : List Bool) (flags : Fin k → List Bool) (x : Fin k → Bool) :
    List.ofFn (fill (recordLayout padded flags).get x) =
      padded ++ ((List.finRange k).flatMap (fun i => true :: x i :: flags i) ++ [false]).reverse := by
  have hmap : List.ofFn (fill (recordLayout padded flags).get x) =
      (recordLayout padded flags).map (Sum.elim id x) := by
    change List.ofFn (Sum.elim id x ∘ (recordLayout padded flags).get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [hmap]
  simp [recordLayout, List.map_flatMap, List.map_reverse, List.map_map, Function.comp_def]

private theorem unique_get_of_count_one {α : Type*} [DecidableEq α] (a : α) (l : List α)
    (hc : l.count a = 1) : ∃! i, l.get i = a := by
  induction l with
  | nil => simp at hc
  | cons b tail ih =>
    by_cases hb : b = a
    · subst b
      have hnot : a ∉ tail := by
        simpa [List.count_cons_self, List.count_eq_zero] using hc
      refine ⟨0, rfl, fun i => ?_⟩
      refine Fin.cases (fun _ => rfl) (fun j h => ?_) i
      exact (hnot (h ▸ tail.get_mem j)).elim
    · have hc' : tail.count a = 1 := by simpa [List.count_cons, hb] using hc
      obtain ⟨j, hj, hjuniq⟩ := ih hc'
      refine ⟨j.succ, hj, fun i => ?_⟩
      refine Fin.cases (fun h => (hb h).elim) (fun t h => ?_) i
      exact congrArg Fin.succ (hjuniq t h)

/-- Each free variable occurs exactly once even after reversal and padding. -/
theorem recordLayout_unique (padded : List Bool) (flags : Fin k → List Bool) :
    ∀ j, ∃! i, (recordLayout padded flags).get i = .inr j := by
  intro j
  let : BEq (Bool ⊕ Fin k) := instBEqOfDecidableEq
  apply unique_get_of_count_one
  have hpinned (bits : List Bool) : (bits.map Sum.inl).count (Sum.inr j) = 0 := by
    apply List.count_eq_zero.mpr
    simp
  have hrecords (indices : List (Fin k)) :
      (indices.flatMap (fun i => Sum.inl true :: Sum.inr i :: (flags i).map Sum.inl)).count
          (.inr j) = indices.count j := by
    induction indices with
    | nil => simp
    | cons i tail ih => simp [List.count_cons, beq_iff_eq, hpinned, ih]
  simp [recordLayout, hpinned, hrecords]

end InterleavedPinning

end VPVNP
end Computability
end OAI
