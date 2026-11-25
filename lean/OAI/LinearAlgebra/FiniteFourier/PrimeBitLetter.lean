import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max

/-! # Rectangles for the first differing bit of two letters

An equality cut records the entire letter. A cut at bit `i` records
the common preceding prefix and the source bit; at the destination
the bit is complemented. Thus equality of records is a rectangle condition.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- A letter over the alphabet of size `2^b`. -/
abbrev BitLetter (b : ℕ) := Fin b → Bool

/-- The data stored for an equality cut or a cut at a particular bit. -/
def BitRecord (b : ℕ) : Option (Fin b) → Type
  | none => BitLetter b
  | some i => (Fin i.val → Bool) × Bool

instance (b : ℕ) (c : Option (Fin b)) : Fintype (BitRecord b c) := by
  cases c <;> dsimp only [BitRecord, BitLetter] <;> infer_instance

instance (b : ℕ) (c : Option (Fin b)) : DecidableEq (BitRecord b c) := by
  cases c <;> dsimp only [BitRecord, BitLetter] <;> infer_instance

/-- The source stores its prefix and its bit at the cut. -/
def leftBitRecord {b : ℕ} (c : Option (Fin b)) (v : BitLetter b) : BitRecord b c :=
  match c with
  | none => v
  | some i => (fun j => v (j.castLE i.isLt.le), v i)

/-- The destination stores its prefix and the complement of its bit at the cut. -/
def rightBitRecord {b : ℕ} (c : Option (Fin b)) (w : BitLetter b) : BitRecord b c :=
  match c with
  | none => w
  | some i => (fun j => w (j.castLE i.isLt.le), !(w i))

/-- The two sides of cut `i` match exactly when `i` is the first differing bit. -/
theorem bitRecord_some_eq_iff {b : ℕ} (v w : BitLetter b) (i : Fin b) :
    leftBitRecord (some i) v = rightBitRecord (some i) w ↔
      (∀ j < i, v j = w j) ∧ v i ≠ w i := by
  change ((fun j : Fin i.val => v (j.castLE i.isLt.le)), v i) =
    ((fun j : Fin i.val => w (j.castLE i.isLt.le)), !(w i)) ↔ _
  rw [Prod.mk.injEq, Bool.eq_not_iff, and_congr_left_iff]
  intro _
  exact ⟨fun h j hj => congrFun h ⟨j.val, hj⟩,
    fun h => funext fun j => h (j.castLE i.isLt.le) j.isLt⟩

/-- Matching cut records come from equal letters precisely for the equality cut. -/
theorem eq_iff_cut_none {b : ℕ} {c : Option (Fin b)} {v w : BitLetter b}
    (h : leftBitRecord c v = rightBitRecord c w) : v = w ↔ c = none := by
  cases c with
  | none => exact iff_of_true h rfl
  | some i =>
    have hne := ((bitRecord_some_eq_iff v w i).mp h).2
    exact iff_of_false (fun he => hne (congrFun he i)) (by simp)

/-- Every ordered pair of letters belongs to exactly one cut. -/
theorem existsUnique_bitCut {b : ℕ} (v w : BitLetter b) :
    ∃! c : Option (Fin b), leftBitRecord c v = rightBitRecord c w := by
  classical
  by_cases hvw : v = w
  · exact ⟨none, hvw, fun c hc => (eq_iff_cut_none hc).mp hvw⟩
  let bad := Finset.univ.filter fun i => v i ≠ w i
  have hbad : bad.Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hvw
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let i := bad.min' hbad
  have hi : (∀ j < i, v j = w j) ∧ v i ≠ w i := by
    refine ⟨fun j hj => by
      by_contra h
      exact hj.not_ge (bad.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)), ?_⟩
    exact (Finset.mem_filter.mp (bad.min'_mem hbad)).2
  refine ⟨some i, (bitRecord_some_eq_iff v w i).mpr hi, ?_⟩
  rintro (_ | j) hc
  · exact (hvw hc).elim
  · obtain ⟨hpre, hd⟩ := (bitRecord_some_eq_iff v w j).mp hc
    congr 1
    exact le_antisymm (le_of_not_gt fun hij => hi.2 (hpre i hij))
      (le_of_not_gt fun hji => hd (hi.1 j hji))

end FiniteFourier
end LinearAlgebra
end OAI
