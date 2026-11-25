import OAI.ThreeFlat.Routing.StableCompactionRank
import OAI.ThreeFlat.BitNetwork.PinMap
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI
/-! # Stable compaction commutes with adding zero rows -/

namespace ThreeFlat.Routing.StableCompaction

/-- Extend a Boolean array to a longer array by filling extra positions with zero. -/
def padRows {n : ℕ} (N : ℕ) (X : Fin n → Bool) (i : Fin N) : Bool :=
  if h : i.val < n then X ⟨i.val,h⟩ else false

@[simp] theorem padRows_castLE {n N : ℕ} (h : n ≤ N) (X : Fin n → Bool) (i : Fin n) :
    padRows N X (i.castLE h) = X i := by
  simp [padRows, i.isLt]

theorem padRows_injective {n N : ℕ} (h : n ≤ N) : Function.Injective (@padRows n N) := by
  intro X Y e
  funext i
  simpa only [padRows_castLE] using congrFun e (i.castLE h)

private theorem active_padRows {n N : ℕ} (h : n ≤ N) (M : Fin n → Bool) :
    active (padRows N M) = (active M).map (Fin.castLEEmb h) := by
  ext i
  constructor
  · intro hi
    have hh := mem_active.mp hi
    by_cases hs : i.val < n
    · refine Finset.mem_map.mpr ⟨⟨i.val,hs⟩,mem_active.mpr ?_,Fin.ext rfl⟩
      simpa [padRows, hs] using hh
    · simp [padRows, hs] at hh
  · intro hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    exact mem_active.mpr ((padRows_castLE h M j).trans (mem_active.mp hj))

private theorem prefixCount_padRows {n N : ℕ} (h : n ≤ N) (M : Fin n → Bool) (i : Fin n) :
    prefixCount (padRows N M) (i.castLE h) = prefixCount M i := by
  unfold prefixCount
  rw [active_padRows h, Finset.filter_map, Finset.card_map]
  rfl

theorem compact_padRows {n N : ℕ} (h : n ≤ N) (M X : Fin n → Bool) :
    compact (padRows N M) (padRows N X) = padRows N (compact M X) := by
  funext j
  have hcard : (active (padRows N M)).card = (active M).card := by
    rw [active_padRows h, Finset.card_map]
  have hn : (active M).card ≤ n := (active M).card_le_univ.trans_eq (Fintype.card_fin n)
  by_cases hs : j.val < (active M).card
  · obtain ⟨i,⟨hi,hr⟩,_⟩ := existsUnique_active_of_prefixCount M ⟨j.val,hs⟩
    have hai : padRows N M (i.castLE h) = true := (padRows_castLE h M i).trans hi
    have hpos : j.val = prefixCount (padRows N M) (i.castLE h) :=
      hr.symm.trans (prefixCount_padRows h M i).symm
    rw [compact_at_prefixCount _ _ hai hpos, padRows_castLE]
    have hjn := hs.trans_le hn
    simp only [padRows, hjn, ↓reduceDIte]
    exact (compact_at_prefixCount M X hi hr.symm).symm
  · have hafter : (active (padRows N M)).card ≤ j.val := hcard.le.trans (Nat.le_of_not_gt hs)
    rw [compact_after _ _ j hafter]
    by_cases hjn : j.val < n
    · simp only [padRows, hjn, ↓reduceDIte]
      exact (compact_after _ _ _ (Nat.le_of_not_gt hs)).symm
    · simp [padRows, hjn]

private def shortRow {N : ℕ} (n : ℕ) (i : Fin N) : Option (Fin n) :=
  if h : i.val < n then some ⟨i.val,h⟩ else none

private def paddingPins (n N : ℕ) : Fin (N + (N+N)) → Option (Fin (n + (n+n))) :=
  Fin.append (fun i => (shortRow n i).map (fun j => j.castAdd (n+n)))
    (Fin.append (fun i => (shortRow n i).map (fun j => Fin.natAdd n (j.castAdd n)))
      (fun i => (shortRow n i).map (fun j => Fin.natAdd n (Fin.natAdd n j))))

private theorem readPaddingPins {n N : ℕ} (M X Y : Fin n → Bool) :
    (fun i => ((paddingPins n N i).map (Fin.append M (Fin.append X Y))).getD false) =
      Fin.append (padRows N M) (Fin.append (padRows N X) (padRows N Y)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · by_cases hj : j.val < n <;>
      simp only [paddingPins, Fin.append_left, shortRow, padRows, hj, ↓reduceDIte,
        Option.map_some, Option.map_none, Option.getD_some, Option.getD_none]
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      by_cases hk : k.val < n <;>
      simp only [paddingPins, Fin.append_left, Fin.append_right, shortRow, padRows, hk, ↓reduceDIte,
        Option.map_some, Option.map_none, Option.getD_some, Option.getD_none]

/-- Restrict a mask, a source array, and a proposed compacted output together. -/
def restrictRows {K : Type*} {N : ℕ} (B : BitNetwork K (N + (N+N))) (n : ℕ) :
    BitNetwork K (n + (n+n)) :=
  B.restrictPins (paddingPins n N)

theorem restrictRows_eval {K : Type*} [CommSemiring K] {n N : ℕ} (h : n ≤ N)
    (B : BitNetwork K (N + (N+N)))
    (correct : ∀ M X Y : Fin N → Bool, B.eval (Fin.append M (Fin.append X Y)) =
      if Y = compact M X then 1 else 0) (M X Y : Fin n → Bool) :
    (restrictRows B n).eval (Fin.append M (Fin.append X Y)) =
      if Y = compact M X then 1 else 0 := by
  classical
  rw [restrictRows, BitNetwork.restrictPins_eval, readPaddingPins, correct,
    compact_padRows h]
  exact ite_congr (propext (padRows_injective h).eq_iff) (fun _ => rfl) (fun _ => rfl)

end ThreeFlat.Routing.StableCompaction

end OAI
