import OAI.Computability.NearSquareRoot.SynchronizedAxisProgram
import OAI.Computability.NearSquareRoot.SynchronizedFixedWord
import OAI.Computability.NearSquareRoot.SynchronizedSlotTable

/-! # Opcode classification through both short-axis lowering passes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.AxisWord
open IntegerMultiplication.Code

/-- The first expansion still permits the Walsh on an internal bit. -/
abbrev LoweredTag (t : ℕ) := t ∈ phaseTags ∨ t = 0 ∨ t = 10 ∨ t = 14

/-- The final expansion routes every Walsh to the half selector. -/
abbrev FixedTag (t : ℕ) := t ∈ phaseTags ∨ t = 0 ∨ t = 10 ∨ t = 18

private theorem orient_tags {w : List Inst} {P : ℕ → Prop}
    (hw : ∀ y ∈ w, P y.1.length) (b : Bool) (y : Inst)
    (hy : y ∈ (if b then adj w else w)) : P y.1.length := by
  cases b with
  | false => exact hw y hy
  | true =>
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact hw z (List.mem_reverse.mp hz)

private theorem threeRounds_tags {P : ℕ → Prop} {t p : ℕ}
    (ht : P t) (hp : P p) (h1 : P (p + 1)) (h2 : P (p + 2)) (arg : Tally) :
    ∀ y ∈ threeRounds t p arg, P y.1.length := by
  simpa [threeRounds, inst, tally] using
    (show P t ∧ P p ∧ P t ∧ P (p + 1) ∧ P t ∧ P (p + 2) from ⟨ht, hp, ht, h1, ht, h2⟩)

theorem lowerInst_tag {x y : Inst} (hx : x.1.length ≤ 9) (hy : y ∈ lowerInst x) :
    LoweredTag y.1.length := by
  by_cases h2 : x.1.length = 2
  · simp only [lowerInst, h2, ite_true] at hy
    exact orient_tags (threeRounds_tags (P := LoweredTag) (t := 14) (p := 15)
      (by decide) (by decide) (by decide) (by decide) _) _ _ hy
  by_cases h3 : x.1.length = 3
  · simp only [lowerInst, h3, ite_true] at hy
    exact orient_tags (threeRounds_tags (P := LoweredTag) (t := 10) (p := 11)
      (by decide) (by decide) (by decide) (by decide) _) _ _ hy
  have hxy : y = x := by simpa [lowerInst, h2, h3] using hy
  subst y
  simp only [LoweredTag, phaseTags, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem loweredRestored_tag (k : Tally) {x : Inst} (hx : x ∈ loweredRestored k) :
    LoweredTag x.1.length := by
  obtain ⟨y, hy, hyx⟩ := List.mem_flatMap.mp hx
  exact lowerInst_tag (restored_fieldsBounded k y hy).1 hyx

theorem fixedInst_tag {k : Tally} {x y : Inst} (hx : LoweredTag x.1.length)
    (hy : y ∈ fixedInst k x) : FixedTag y.1.length := by
  by_cases ht : x.1.length = 14
  · by_cases ha : x.2.1.length < k.length
    · simp only [fixedInst, ht, ha, ite_true] at hy
      apply orient_tags (w := [inst 18 x.2.1, inst 10, inst 18 x.2.1]) _ _ _ hy
      simp [inst, tally, FixedTag]
    · simp [fixedInst, ht, ha] at hy
  · have hxy : y = x := by simpa [fixedInst, ht] using hy
    subst y
    rcases hx with hp | h | h | h
    · exact Or.inl hp
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact (ht h).elim

theorem fixedWord_tag (k : Tally) {x : Inst} (hx : x ∈ fixedWord k) :
    FixedTag x.1.length := by
  obtain ⟨y, hy, hyx⟩ := List.mem_flatMap.mp hx
  exact fixedInst_tag (loweredRestored_tag k hy) hyx

theorem fixedWord_tag_ne_fourteen (k : Tally) {x : Inst} (hx : x ∈ fixedWord k) :
    x.1.length ≠ 14 := by
  have h := fixedWord_tag k hx
  rintro he
  rw [he] at h
  exact (by decide : ¬ FixedTag 14) h

end ShortFourier.AxisWord

end NearSquareRoot
end Computability
end OAI
