import OAI.ThreeFlat.Diagonal.BucketIntervalCodes

namespace OAI
/-! # Natural-address decoding of a finite group-counter table -/

namespace ThreeFlat.Diagonal.BucketFiniteLabels

open HistoryContraction TickGroupIntervals BucketIntervalCodes

variable {I : Type*} {d : ℕ}

/-- The four words retain their numerical meaning when the group index
is read as its physical ordinal in the counter array. -/
def decode (r : BucketRow (Fin d)) : Interval := ⟨r.group.val,r.lo,r.hi,r.offset⟩

theorem pack (group : I → Fin d) (bs : List (Bucket I)) (c : Fin d → ℕ) (a : ℕ → ℕ)
    (same : ∀ j, c j = a j.val) :
    (BucketRows.pack group c bs).map decode = intervals (fun i => (group i).val) a bs := by
  induction bs generalizing c a with
  | nil => rfl
  | cons b bs ih =>
    change decode (BucketRows.row group c b) :: (BucketRows.pack group (BucketRows.bump group c b) bs).map decode =
      interval (BucketRows.row (fun i => (group i).val) a b) ::
        intervals (fun i => (group i).val) (BucketRows.bump (fun i => (group i).val) a b) bs
    apply congrArg₂ List.cons
    · change (⟨(group b.site).val,b.lo,b.hi,c (group b.site)⟩ : Interval) =
        ⟨(group b.site).val,b.lo,b.hi,a (group b.site).val⟩
      rw [same]
    · apply ih
      intro j
      by_cases h : j = group b.site
      · subst j
        simp only [BucketRows.bump,Function.update_self,same]
      · have hv : j.val ≠ (group b.site).val := fun v => h (Fin.ext v)
        simpa only [BucketRows.bump,Function.update_of_ne h,Function.update_of_ne hv] using same j

theorem canonical (group : I → Fin d) (bs : List (Bucket I)) :
    (BucketRows.pack group (fun _ => 0) bs).map decode =
      intervals (fun i => (group i).val) (fun _ => 0) bs :=
  pack group bs _ _ (fun _ => rfl)

theorem count (group : I → Fin d) (bs : List (Bucket I)) (g : Fin d) :
    BucketRows.count group bs g = BucketRows.count (fun i => (group i).val) bs g.val := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change (if group b.site=g then b.size else 0)+BucketRows.count group bs g =
      (if (group b.site).val=g.val then b.size else 0)+BucketRows.count (fun i => (group i).val) bs g.val
    by_cases h : group b.site=g
    · simp only [h,ite_true,ih]
    · have hv : (group b.site).val ≠ g.val := fun v => h (Fin.ext v)
      simp only [ite_eq_right h,ite_eq_right hv,ih]

end ThreeFlat.Diagonal.BucketFiniteLabels

end OAI
