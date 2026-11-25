import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCostHistorical

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace GenerationCost

variable {ι α : Type} {β : ι → Type}

/-- Serialize a function restricted to a list, preserving the list order. -/
private def collect (emit : (i : ι) → β i → α) :
    (is : List ι) → ((i : ι) → i ∈ is → β i) → List α
  | [], _ => []
  | i :: is, g => emit i (g i List.mem_cons_self) ::
      collect emit is (fun j hj => g j (List.mem_cons_of_mem i hj))

private theorem collect_total (emit : (i : ι) → β i → α) (g : (i : ι) → β i) (is : List ι) :
    collect emit is (fun i _ => g i) = is.map (fun i => emit i (g i)) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [collect,ih]

private theorem collect_pi_cons [DecidableEq ι] (emit : (i : ι) → β i → α)
    (i : ι) (is : List ι) (hi : i ∉ is) (b : β i) (g : (j : ι) → j ∈ is → β j) :
    collect emit (i::is) (List.Pi.cons i is b g) = emit i b :: collect emit is g := by
  have ht : (fun j (hj : j ∈ is) => List.Pi.cons i is b g j (List.mem_cons_of_mem i hj)) = g := by
    funext j hj
    have hn : j ≠ i := fun h => hi (h ▸ hj)
    simp [List.Pi.cons_def,hn]
  simp only [collect,ht]
  congr 2
  simp [List.Pi.cons_def]

/-- A no-duplicate index traversal reads the head coordinate before the tail
of a function in `List.pi`, which is the same order as `boundedProduct`. -/
private theorem pi_cartesian [DecidableEq ι] (emit : (i : ι) → β i → α) (choices : (i : ι) → List (β i))
    (cap : ℕ) (is : List ι) (hn : is.Nodup) (hc : is.length ≤ cap) :
    (List.pi is choices).map (collect emit is) =
      boundedProduct α cap (is.map (fun i => (choices i).map (emit i))) := by
  induction cap generalizing is with
  | zero =>
    have hi : is = [] := List.length_eq_zero_iff.mp (by omega)
    subst is; rfl
  | succ cap ih =>
    cases is with
    | nil => rfl
    | cons i is =>
      have hm := List.nodup_cons.mp hn
      have hr := ih is hm.2 (by simpa using hc)
      simp only [List.pi_cons,List.map_flatMap,List.map_cons,boundedProduct,cross,List.flatMap_map]
      rw [←hr]
      simp [List.map_map,Function.comp_def,collect_pi_cons emit i is hm.1]

/-- The option list used in the original `FinEnum` cell construction. -/
def referenceRow (s : Finset ℚ) : List (Cells.Cell s) :=
  none :: (s.attach.sort (· ≤ ·)).flatMap fun θ => [some (θ,false),some (θ,true)]

private theorem attached_sort_val (s : Finset ℚ) :
    (s.attach.sort (· ≤ ·)).map Subtype.val = s.sort (· ≤ ·) := by
  have h := Finset.map_sort (Function.Embedding.subtype (· ∈ s)) s.attach (· ≤ ·) (· ≤ ·)
    (fun _ _ _ _ => Iff.rfl)
  simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using h

private theorem row_serialize (s : Finset ℚ) :
    (referenceRow s).map wireCell = rowChoices (s.sort (· ≤ ·)) := by
  rw [←attached_sort_val s]
  simp [referenceRow,rowChoices,wireCell,List.map_flatMap]

theorem reference_pi_cartesian {n cap : ℕ} (s : Experts.Feature n → Finset ℚ) (hc : n*n ≤ cap) :
    ((List.pi (FinEnum.toList (Experts.Feature n)) (fun f => referenceRow (s f))).map
      (fun g => (fun f => g f (FinEnum.mem_toList f) : Experts.Code s))).map serializeCell =
      historicalCodes cap (historyRows s) := by
  let fs := FinEnum.toList (Experts.Feature n)
  have hn : fs.Nodup := FinEnum.nodup_toList
  have hlen : fs.length ≤ cap := by
    simp only [fs, FinEnum.toList, List.length_map, List.length_finRange,FinEnum.card_eq_fintypeCard]
    simpa [Experts.Feature] using hc
  let emit (f : Experts.Feature n) : Cells.Cell (s f) → RawCell ℚ := wireCell
  have h := pi_cartesian emit (fun f => referenceRow (s f)) cap fs hn hlen
  rw [List.map_map]
  change List.map _ (List.pi fs _) = boundedProduct _ cap ((fs.map _).map rowChoices)
  calc
    List.map _ (List.pi fs _) = (List.pi fs (fun f => referenceRow (s f))).map (collect emit fs) := by
      apply List.map_congr_left
      intro g _
      exact (collect_total emit (fun f => g f (FinEnum.mem_toList f)) fs).symm
    _ = _ := by
      rw [h,List.map_map]
      simp [emit,Function.comp_def,row_serialize]

end GenerationCost
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
