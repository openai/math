import OAI.Hierarchy.TaggedSweep
import OAI.Hierarchy.TaggedSortedKeys
import OAI.Hierarchy.TaggedStableObservations

namespace OAI
/-! # Sorting a block preserves the subsequence of each real digit -/

namespace Hierarchy.Tagged.Radix
open ThreeFlat Routing SortNetwork SortedBlock
open scoped Classical
noncomputable section
variable {d w : ℕ}

def observeRow (real : Fin w) (digit : Fin d → Fin w) (a : ℕ) (z : Bits w) : List (Bits w) :=
  if z real = true ∧ readKey digit z = a then [z] else []

theorem sweep_rows {n : ℕ} (x : Fin n → Bits w) (real : Fin w) (digit : Fin d → Fin w) (a : ℕ) :
    sweep n (fun i => observeRow real digit a (x i)) = bucket (readKey digit) a ((List.ofFn x).filter fun z => z real) := by
  rw [sweep_eq_flatMap]
  have aux (xs : List (Fin n)) : xs.flatMap (fun i => observeRow real digit a (x i)) =
      bucket (readKey digit) a ((xs.map x).filter fun z => z real) := by
    induction xs with
    | nil => rfl
    | cons i xs ih => cases hb : x i real <;> by_cases hk : readKey digit (x i) = a <;> simpa [bucket,observeRow,hb,hk] using ih
  simpa [List.map_ofFn] using aux (List.ofFn id)

theorem localSort_buckets {l : ℕ} (x : Records l w) (real dummy : Fin w) (digit : Fin d → Fin w) (a : ℕ)
    (flags : ∀ i, x i dummy = !(x i real)) :
    sweep (2^l) (fun i => observeRow real digit a (stable (PassShape.maskedDigit digit dummy) x i)) =
      sweep (2^l) (fun i => observeRow real digit a (x i)) := by
  let key (i : Row l) := addressEquiv (d+1) (x i ∘ PassShape.maskedDigit digit dummy)
  let see (i : Row l) := observeRow real digit a (x i)
  by_cases low : a < 2^d
  · let pick : Row (d+1) := ⟨a,low.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ d))⟩
    have confined (i : Row l) (bad : key i ≠ pick) : see i=[] := by
      simp only [see,observeRow,ite_eq_right_iff]
      rintro ⟨hr,eq⟩
      apply False.elim (bad (Fin.ext ?_))
      change readKey (PassShape.maskedDigit digit dummy) (x i) = a
      simp [masked_value,flags,hr,eq]
    have go := stable_observe_packs key pick see confined
    simpa only [sweep,List.flatMap_def,List.map_ofFn,Function.comp_def,id_eq,see,stable,key] using go
  · have zero (i : Row l) : see i=[] := by
      have below := (addressEquiv d (x i ∘ digit)).isLt
      change readKey digit (x i) < 2^d at below
      simp [see,observeRow,show readKey digit (x i) ≠ a by omega]
    simp only [sweep_eq_flatMap]
    have off (i : Row l) : observeRow real digit a (stable (PassShape.maskedDigit digit dummy) x i)=[] := zero _
    rw [List.flatMap_eq_nil_iff.mpr (fun i _ => off i), List.flatMap_eq_nil_iff.mpr (fun i _ => zero i)]

end
end Hierarchy.Tagged.Radix

end OAI
