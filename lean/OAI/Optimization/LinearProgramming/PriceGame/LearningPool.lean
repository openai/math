import OAI.Optimization.LinearProgramming.PriceGame.LearningSkeleton
import OAI.Optimization.LinearProgramming.PriceGame.LearningSelections
import OAI.Optimization.LinearProgramming.PriceGame.LearningCatalog
import OAI.Optimization.LinearProgramming.PriceGame.Skeletons

/-! # The public expert list for one trial of the price game -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace Pool

open Finset States.Mass

/-- All feasible comparison cells of the historical probes on one actual skeleton. -/
def forSkeleton {N} (R : ℕ) (s : Skeleton N) (probes : List (Probe N)) : List (Expert N) :=
  (Experts.generate R 0 (Compact.thresholds s probes)).map fun v => ⟨s,Compact.unpack s v⟩

/-- The public list of new expert entries at the start of a trial. -/
def batch (N R : ℕ) (probes : List (Probe N)) : List (Expert N) :=
  (Skeleton.enumerate N).flatMap fun s => forSkeleton R s probes

/-- The representative picked for the hidden integer assignment in the proof. -/
def selectedCompact {N} (R : ℕ) (s : Skeleton N) (probes : List (Probe N)) (P : Fin N → ℤ) :
    Compact.Coord s → ℚ :=
  Selections.selected R 0 (Compact.thresholds s probes) (Compact.pack s P)

def selectedExpert {N} (R : ℕ) (s : Skeleton N) (probes : List (Probe N)) (P : Fin N → ℤ) :
    Expert N := ⟨s, Compact.unpack s (selectedCompact R s probes P)⟩

theorem selectedCompact_zero {N} (R : ℕ) (s : Skeleton N) (probes : List (Probe N))
    (P : Fin N → ℤ) : selectedCompact R s probes P 0 = 0 := representative_anchor _

theorem selected_mem_forSkeleton {N} (R : ℕ) (s : Skeleton N) (probes : List (Probe N))
    (P : Fin N → ℤ) (hP : ∀ i, 1 ≤ P i ∧ P i ≤ (R : ℤ)+1) :
    selectedExpert R s probes P ∈ forSkeleton R s probes := by
  exact List.mem_map.mpr ⟨selectedCompact R s probes P,
    Selections.selected_mem _ (Compact.pack_zero _ _) (Compact.pack_int_box s R P hP),rfl⟩

theorem selected_mem_batch {N} (R : ℕ) (s : Skeleton N) (probes : List (Probe N))
    (P : Fin N → ℤ) (hP : ∀ i, 1 ≤ P i ∧ P i ≤ (R : ℤ)+1) :
    selectedExpert R s probes P ∈ batch N R probes :=
  List.mem_flatMap.mpr ⟨s,Skeleton.mem_enumerate _,selected_mem_forSkeleton _ _ _ _ hP⟩

/-- The selected representative has the same order and ties as the hidden data in every
comparison made on its skeleton in the available transcript. -/
theorem selected_history_agrees {N} (R : ℕ) (s : Skeleton N) (ps : List (Probe N))
    (P : Fin N → ℤ) (hP : ∀ i, 1 ≤ P i ∧ P i ≤ (R : ℤ)+1) (t : Test N)
    (ht : t ∈ ps.flatMap s.testsAt) :
    compare (featureValue (selectedExpert R s ps P).raw t.feature) t.threshold =
      compare (featureValue (fun i => (P i : ℚ)) t.feature) t.threshold := by
  let ij := Compact.endpoints s t.feature
  have h := Selections.selected_agrees (Compact.thresholds s ps) (Compact.pack_zero s P)
    (Compact.pack_int_box s R P hP) ij t.threshold (Compact.threshold_mem s ps t ht)
  change compare (featureValue (Compact.unpack s (selectedCompact R s ps P)) t.feature) _ = _
  rw [Compact.featureValue_unpack s ps t ht _ (selectedCompact_zero _ _ _ _),
    Compact.featureValue_pack s ps t ht, ← Compact.pack_intCast]
  exact h

theorem entry_box {N R : ℕ} {ps : List (Probe N)} {e : Expert N} (h : e ∈ batch N R ps)
    (i : Fin N) : 1 ≤ e.raw i ∧ e.raw i ≤ (R : ℚ)+1 := by
  obtain ⟨s,_,he⟩ := List.mem_flatMap.mp h
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
  exact Compact.unpack_box s R v (Experts.generated_sound hv).2.1 i

/-- Number of possible expert entries for a skeleton, including inactive copied goods.
Only the fixed `66²` compact feature pairs contribute to the exponent. -/
theorem length_forSkeleton_le {N} (R : ℕ) (s : Skeleton N) (ps : List (Probe N)) :
    (forSkeleton R s ps).length ≤ (2 * (ps.length * 4160) + 1) ^ (66^2 : ℕ) := by
  rw [forSkeleton,List.length_map]
  refine (Experts.length_generate_le R 0 _ _ (Compact.thresholds_card_le s ps)).trans ?_
  apply Nat.pow_le_pow_right (by positivity)
  have hc : s.sources.card+1 ≤ 66 := by have := Skeleton.card_sources_le s; omega
  exact Nat.mul_le_mul hc hc

private theorem flatMap_length_le {α β : Type*} (xs : List α) (f : α → List β) (b : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ b) : (xs.flatMap f).length ≤ xs.length * b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,one_mul]
    exact (Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))).trans_eq (Nat.add_comm ..)

theorem length_batch_le (N R : ℕ) (ps : List (Probe N)) :
    (batch N R ps).length ≤ (Skeleton.enumerate N).length * (2 * (ps.length * 4160) + 1) ^ (66^2 : ℕ) :=
  flatMap_length_le _ _ _ (fun s _ => length_forSkeleton_le R s ps)

/-- The total list size includes all previous entries as distinct permanent IDs. -/
theorem catalogue_size (N R T probesPerTrial : ℕ) (hist : ℕ → List (Probe N))
    (hh : ∀ t < T, (hist t).length ≤ T*probesPerTrial) :
    (Catalog.entries (fun t => batch N R (hist t)) T).length ≤
      T * ((Skeleton.enumerate N).length * (2 * (T*probesPerTrial*4160) + 1) ^ (66^2 : ℕ)) := by
  apply Catalog.entries_size_bound
  intro t ht
  refine (length_batch_le N R _).trans (Nat.mul_le_mul_left _ ?_)
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right 4160 (hh t ht))) 1

/-- The numerical ID returned here can still be read at every later trial, with the same
raw values and the same skeleton. No equality test on experts is required. -/
theorem selected_has_persistent_id {N} (R : ℕ) (s : Skeleton N) (hist : ℕ → List (Probe N))
    (P : Fin N → ℤ) (hP : ∀ i, 1 ≤ P i ∧ P i ≤ (R : ℤ)+1) (first : ℕ) :
    ∃ id : ℕ, ∀ t, first < t → (Catalog.entries (fun t => batch N R (hist t)) t)[id]? =
      some (selectedExpert R s (hist first) P) := by
  have hm := selected_mem_batch R s (hist first) P hP
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hm
  refine ⟨Catalog.freshId (fun t => batch N R (hist t)) first j,?_⟩
  intro t ht
  exact (Catalog.fresh_lookup (fun t => batch N R (hist t)) ht j).trans (congrArg some hj)

end Pool
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
