import OAI.Optimization.LinearProgramming.PriceGame.LearningExperts
import Mathlib.Data.List.OfFn
import Mathlib.Data.Multiset.Pi

/-! # The reference enumeration visits its cells in Cartesian product order -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace Experts

open Finset

/-- Explicit options for one sorted threshold row. Below-all is first; each predecessor
then contributes its above-interval and equality cases, in that order. -/
def orderedChoices (s : Finset ℚ) : List (Cells.Cell s) :=
  none :: (s.attach.sort (· ≤ ·)).flatMap fun θ => [some (θ,false),some (θ,true)]

private theorem choices_mem (s : Finset ℚ) (c : Cells.Cell s) : c ∈ orderedChoices s := by
  cases c with
  | none => simp [orderedChoices]
  | some pair => obtain ⟨θ,b⟩ := pair; cases b <;> simp [orderedChoices]

private theorem length_double {α β : Type*} (xs : List α) (a b : α → β) :
    (xs.flatMap fun x => [a x,b x]).length = 2*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih,Nat.mul_add]

private theorem choices_nodup (s : Finset ℚ) : (orderedChoices s).Nodup := by
  rw [List.nodup_iff_length_dedup_eq, ← List.card_toFinset]
  have h : (orderedChoices s).toFinset = univ := by ext c; simp [choices_mem s c]
  rw [h,card_univ,Cells.card_cell,orderedChoices,List.length_cons,length_double]
  simp

private theorem enum_ofList_eq {α : Type*} [DecidableEq α] (xs : List α) (h : ∀ a, a ∈ xs) :
    @FinEnum.toList α (FinEnum.ofList xs h) = xs.dedup := by
  change (List.finRange xs.dedup.length).map xs.dedup.get = xs.dedup
  simp only [List.finRange,List.map_ofFn]
  exact List.ofFn_get _

private theorem piEnum_nodup {ι : Type*} [FinEnum ι] {β : ι → Type*} [∀ i, FinEnum (β i)] :
    (List.Pi.enum β).Nodup := by
  let xs := FinEnum.toList ι
  let ys := fun i => FinEnum.toList (β i)
  have hx : ((xs : List ι) : Multiset ι).Nodup := FinEnum.nodup_toList
  have hy (i : ι) (_ : i ∈ xs) : ((ys i : List (β i)) : Multiset (β i)).Nodup := FinEnum.nodup_toList
  have hm := Multiset.Nodup.pi (t := fun i => ((ys i : List (β i)) : Multiset (β i))) hx hy
  rw [Multiset.pi_coe] at hm
  have hn : (List.pi xs ys).Nodup := hm
  apply hn.map
  intro g g' h
  funext i hi
  exact congrFun h i

private theorem toList_pi_order {ι : Type*} [FinEnum ι] {β : ι → Type*} [∀ i, FinEnum (β i)] :
    FinEnum.toList ((i : ι) → β i) = (List.pi (FinEnum.toList ι) (fun i => FinEnum.toList (β i))).map
      (fun g i => g i (FinEnum.mem_toList i)) := by
  change @FinEnum.toList _ (FinEnum.ofList (List.Pi.enum β) (fun f => List.Pi.mem_enum f)) = _
  exact (enum_ofList_eq _ _).trans (List.dedup_eq_self.mpr piEnum_nodup)

/-- The `FinEnum` deduplication operations are both inert, including when multiple
features or equal threshold values interact. This equality preserves persistent entry IDs. -/
theorem codes_eq_pi {n : ℕ} (s : Feature n → Finset ℚ) :
    codes s = ((List.pi (FinEnum.toList (Feature n)) (fun f => orderedChoices (s f))).map
      (fun g f => g f (FinEnum.mem_toList f))) := by
  let _ (f : Feature n) : FinEnum (Cells.Cell (s f)) := FinEnum.ofList (orderedChoices (s f)) (choices_mem _)
  change FinEnum.toList ((f : Feature n) → Cells.Cell (s f)) = _
  rw [toList_pi_order]
  have hchoices (f : Feature n) : FinEnum.toList (Cells.Cell (s f)) = orderedChoices (s f) :=
    (enum_ofList_eq (orderedChoices (s f)) (choices_mem _)).trans (List.dedup_eq_self.mpr (choices_nodup _))
  rw [show (fun f : Feature n => FinEnum.toList (Cells.Cell (s f))) = (fun f => orderedChoices (s f)) from funext hchoices]

end Experts
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
