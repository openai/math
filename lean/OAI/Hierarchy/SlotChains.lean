import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace OAI
/-! # Counting the slot sets at successive marked formula gates -/

namespace Hierarchy.FormulaSlotChains

open scoped BigOperators Classical
noncomputable section

variable {α : Type*} [DecidableEq α]

/-- A boundary chain chooses a subset of the remaining slots at each
successive mark. The list gives the absolute size caps on those subsets. -/
def slotChains (S : Finset α) (bounds : List ℕ) : Finset (List (Finset α)) :=
  match bounds with
  | [] => {[]}
  | b::bs => (S.powerset.filter (fun T => T.card≤b)).biUnion fun T =>
      (slotChains T bs).image (List.cons T)

/-- The conditions visible on a list of slot sets along a marked path. -/
def Fits (S : Finset α) (bounds : List ℕ) (slots : List (Finset α)) : Prop :=
  match bounds, slots with
  | [], [] => True
  | b::bs, T::ts => T⊆S ∧ T.card≤b ∧ Fits T bs ts
  | _, _ => False

theorem mem_slotChains (S : Finset α) (bounds : List ℕ) (slots : List (Finset α)) :
    slots ∈ slotChains S bounds ↔ Fits S bounds slots := by
  induction bounds generalizing S slots with
  | nil => cases slots <;> simp [slotChains,Fits]
  | cons b bs ih =>
    cases slots with
    | nil => simp [slotChains,Fits]
    | cons T ts =>
      constructor
      · intro hit
        obtain ⟨U,hU,rest⟩ := Finset.mem_biUnion.mp hit
        obtain ⟨us,hus,eqn⟩ := Finset.mem_image.mp rest
        obtain ⟨rfl,rfl⟩ := List.cons.inj eqn
        have chosen := Finset.mem_filter.mp hU
        exact ⟨Finset.mem_powerset.mp chosen.1,chosen.2,(ih _ _).mp hus⟩
      · rintro ⟨sub,small,hits⟩
        exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr sub,small⟩,
          Finset.mem_image.mpr ⟨ts,(ih _ _).mpr hits,rfl⟩⟩

theorem card_slotChains_le (S : Finset α) (bounds : List ℕ) :
    (slotChains S bounds).card ≤ 2^(S.card+bounds.sum) := by
  induction bounds generalizing S with
  | nil =>
    simp only [slotChains,Finset.card_singleton,List.sum_nil,Nat.add_zero]
    exact Nat.two_pow_pos S.card
  | cons b bs ih =>
    let choices := S.powerset.filter (fun T => T.card≤b)
    have count : choices.card ≤ 2^S.card := by
      simpa [choices] using Finset.card_le_card (Finset.filter_subset (fun T : Finset α => T.card≤b) S.powerset)
    calc
      (slotChains S (b::bs)).card
          ≤ ∑ T ∈ choices, ((slotChains T bs).image (List.cons T)).card := Finset.card_biUnion_le
      _ ≤ ∑ _T ∈ choices, 2^(b+bs.sum) := by
        apply Finset.sum_le_sum
        intro T hT
        have cap := (Finset.mem_filter.mp hT).2
        exact Finset.card_image_le.trans ((ih T).trans
          (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right cap _)))
      _ = choices.card * 2^(b+bs.sum) := by simp
      _ ≤ 2^S.card * 2^(b+bs.sum) := Nat.mul_le_mul_right _ count
      _ = 2^(S.card+(b::bs).sum) := by rw [←pow_add,List.sum_cons]

/-- Successive thresholds are ⌊d/2⌋, ⌊d/4⌋, and so on. -/
def tailCaps (d : ℕ) : ℕ → List ℕ
  | 0 => []
  | t+1 => d/2 :: tailCaps (d/2) t

@[simp] theorem length_tailCaps (d t : ℕ) : (tailCaps d t).length=t := by
  induction t generalizing d with
  | zero => rfl
  | succ t ih => simp [tailCaps,ih]

theorem getElem_tailCaps (d t : ℕ) (i : Fin t) :
    (tailCaps d t)[i.val]'(by simp)=d / 2^(i.val+1) := by
  induction t generalizing d with
  | zero => exact Fin.elim0 i
  | succ t ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simpa [tailCaps,Nat.div_div_eq_div_mul,pow_succ',Nat.mul_assoc] using ih (d/2) j

theorem sum_tailCaps_le (d t : ℕ) : (tailCaps d t).sum ≤ d := by
  induction t generalizing d with
  | zero => simp [tailCaps]
  | succ t ih =>
    simp only [tailCaps,List.sum_cons]
    have bound := ih (d/2)
    omega

/-- With d initial slots, at most 2^(2d) different boundary chains occur,
independently of the number of marks and the balanced formula height. -/
theorem card_marked_chains (S : Finset α) (t : ℕ) :
    (slotChains S (tailCaps S.card t)).card ≤ 2^(2*S.card) := by
  apply (card_slotChains_le S _).trans
  apply Nat.pow_le_pow_right (by decide)
  have bound := sum_tailCaps_le S.card t
  omega

end
end Hierarchy.FormulaSlotChains

end OAI
