import OAI.Computability.VPVNP.ExactOneFirst
import OAI.Computability.VPVNP.ExactOneClauses

/-!
# The parsimonious conversion from CNF to exact-one constraints

For a satisfying assignment, the selector in each clause marks its first
satisfied literal. This fixes the filler of every implication. Conversely an
assignment meeting the exact-one constraints must use these same selectors
and fillers. Restricting to the input bits therefore gives a bijection.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

open HardnessCNF

variable {k : ℕ}

private def hit (φ : CNF k) (y : Fin k → Bool) (c : Fin φ.length) (i : Fin (φ[c].length)) :
    Bool := y (φ[c][i]).1 == (φ[c][i]).2

private theorem satisfies_iff_hits (φ : CNF k) (y : Fin k → Bool) :
    Satisfies φ y ↔ ∀ c : Fin φ.length, ∃ i, hit φ y c i = true := by
  simp only [Satisfies, List.forall_mem_iff_get, List.exists_mem_iff_get, hit, beq_iff_eq]
  rfl

private theorem firstMatch_iff_needed (φ : CNF k) (y : Fin k → Bool) (c : Fin φ.length)
    (i : Fin (φ[c].length)) :
    firstMatch (hit φ y c) i = true ↔ ∀ j ≤ i, needed φ y c i j = true := by
  rw [firstMatch_iff]
  constructor
  · rintro ⟨hi, hprefix⟩ j hj
    rcases eq_or_lt_of_le hj with rfl | hlt
    · simpa [needed, hit] using hi
    · have h := hprefix j hlt
      simpa [needed, hit, hlt.ne] using h
  · intro h
    refine ⟨by simpa [needed, hit] using h i le_rfl, fun j hj => ?_⟩
    simpa [needed, hit, hj.ne] using h j hj.le

/-- The unique extension of a satisfying assignment sets the first-match selectors
and the complementary filler in each active implication. -/
private noncomputable def encode (φ : CNF k) (y : Fin k → Bool) : Fin (width φ) → Bool :=
  fun v => ((index φ).symm v).elim y (Sum.elim
    (fun ⟨c, i⟩ => firstMatch (hit φ y c) i)
    (fun ⟨c, i, j⟩ => if j ≤ i then needed φ y c i j && !(firstMatch (hit φ y c) i) else false))

@[simp] private theorem encode_data (φ : CNF k) (y : Fin k → Bool) (v : Fin k) :
    encode φ y (data φ v) = y v := by simp [encode, data]

@[simp] private theorem original_encode (φ : CNF k) (y : Fin k → Bool) :
    original φ (encode φ y) = y := by funext i; exact encode_data _ _ i

@[simp] private theorem encode_selector (φ : CNF k) (y : Fin k → Bool) (c : Fin φ.length)
    (i : Fin (φ[c].length)) : encode φ y (selector φ c i) = firstMatch (hit φ y c) i := by
  simp [encode, selector]

@[simp] private theorem encode_filler (φ : CNF k) (y : Fin k → Bool) (c : Fin φ.length)
    (i j : Fin (φ[c].length)) :
    encode φ y (filler φ c i j) =
      if j ≤ i then needed φ y c i j && !(firstMatch (hit φ y c) i) else false := by
  simp [encode, filler]

private theorem holds_encode (φ : CNF k) (y : Fin k → Bool) (hy : Satisfies φ y) :
    Holds (augment φ) (encode φ y) := by
  apply (holds_augment_iff φ _).2
  refine ⟨fun c => ?_, fun c i j => ?_⟩
  · simp only [selectedOnce, encode_selector, countP_finRange_eq_one]
    exact existsUnique_firstMatch _ ((satisfies_iff_hits φ y).1 hy c)
  · simp only [original_encode, encode_selector, encode_filler]
    by_cases hji : j ≤ i
    · simp only [hji, ite_true, and_true]
      exact fun hs => (firstMatch_iff_needed φ y c i).1 hs j hji
    · simp [hji]

private theorem selector_is_first (φ : CNF k) (x : Fin (width φ) → Bool)
    (hx : Holds (augment φ) x) (c : Fin φ.length) (i : Fin (φ[c].length)) :
    x (selector φ c i) = firstMatch (hit φ (original φ x) c) i := by
  obtain ⟨honce, hpairs⟩ := (holds_augment_iff φ x).1 hx
  have hfirst (a : Fin (φ[c].length)) (ha : x (selector φ c a) = true) :
      firstMatch (hit φ (original φ x) c) a = true := by
    apply (firstMatch_iff_needed _ _ _ _).2
    intro j hj
    have hp := hpairs c a j
    simp only [hj, ite_true] at hp
    exact hp.1 ha
  apply Bool.eq_iff_iff.mpr
  refine ⟨hfirst i, fun hi => ?_⟩
  obtain ⟨a, ha, _⟩ := (countP_finRange_eq_one _).1 (honce c)
  exact firstMatch_unique _ (hfirst a ha) hi ▸ ha

private theorem satisfies_original (φ : CNF k) (x : Fin (width φ) → Bool)
    (hx : Holds (augment φ) x) : Satisfies φ (original φ x) := by
  apply (satisfies_iff_hits _ _).2
  intro c
  obtain ⟨i, hi, _⟩ :=
    (countP_finRange_eq_one _).1 (((holds_augment_iff φ x).1 hx).1 c)
  rw [selector_is_first _ _ hx] at hi
  exact ⟨i, ((firstMatch_iff _ _).1 hi).1⟩

private theorem encode_original (φ : CNF k) (x : Fin (width φ) → Bool)
    (hx : Holds (augment φ) x) : encode φ (original φ x) = x := by
  funext v
  obtain ⟨s, rfl⟩ := (index φ).surjective v
  rcases s with v | ⟨c, i⟩ | ⟨c, i, j⟩
  · exact encode_data φ (original φ x) v
  · exact (encode_selector φ (original φ x) c i).trans (selector_is_first φ x hx c i).symm
  · change encode φ (original φ x) (filler φ c i j) = x (filler φ c i j)
    rw [encode_filler, ← selector_is_first φ x hx]
    have hf := ((holds_augment_iff φ x).1 hx).2 c i j
    by_cases hji : j ≤ i
    · simp only [hji, ite_true] at hf ⊢
      exact hf.2.symm
    · simp only [hji, ite_false] at hf ⊢
      exact hf.symm

/-- Each satisfying input has exactly one extension to the exact-one formula. -/
noncomputable def solutionsEquiv (φ : CNF k) :
    {x : Fin (width φ) → Bool // Holds (augment φ) x} ≃
      {y : Fin k → Bool // Satisfies φ y} where
  toFun x := ⟨original φ x.val, satisfies_original _ _ x.property⟩
  invFun y := ⟨encode φ y.val, holds_encode _ _ y.property⟩
  left_inv x := Subtype.ext (encode_original _ _ x.property)
  right_inv y := Subtype.ext (original_encode φ y.val)

@[simp] theorem solutionsEquiv_apply (φ : CNF k) (x) :
    (solutionsEquiv φ x).val = original φ x.val := rfl

end ExactOne

end VPVNP
end Computability
end OAI
