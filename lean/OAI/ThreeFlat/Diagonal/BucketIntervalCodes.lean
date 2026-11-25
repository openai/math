import OAI.ThreeFlat.Diagonal.HistoryBucketRows
import OAI.ThreeFlat.Diagonal.TickGroupIntervals

namespace OAI
/-! # Decoding the physical comparison map from the original bucket rows -/

namespace ThreeFlat.Diagonal.BucketIntervalCodes

open TickGroupIntervals HistoryContraction

variable {I : Type*}

def interval (r : BucketRow ℕ) : Interval := ⟨r.group,r.lo,r.hi,r.offset⟩

def intervals (group : I → ℕ) (acc : ℕ → ℕ) (bs : List (Bucket I)) : List Interval :=
  (BucketRows.pack group acc bs).map interval

def overlaps (group : I → ℕ) (g x : ℕ) (b : Bucket I) : Prop :=
  group b.site = g ∧ b.lo ≤ x ∧ x < b.hi

instance (group : I → ℕ) (g x : ℕ) (b : Bucket I) : Decidable (overlaps group g x b) := by
  unfold overlaps
  infer_instance

theorem code_zero_iff (group : I → ℕ) (acc : ℕ → ℕ) (bs : List (Bucket I)) (g x : ℕ) :
    pairCode g x (intervals group acc bs) = 0 ↔ ∀ b ∈ bs, ¬overlaps group g x b := by
  induction bs generalizing acc with
  | nil => simp [intervals,BucketRows.pack,pairCode]
  | cons b bs ih =>
    change (if (interval (BucketRows.row group acc b)).code g x = 0 then
      pairCode g x (intervals group (BucketRows.bump group acc b) bs) else
      (interval (BucketRows.row group acc b)).code g x) = 0 ↔ _
    by_cases h : overlaps group g x b
    · have nz : (interval (BucketRows.row group acc b)).code g x ≠ 0 := by
        change (if overlaps group g x b then 1+acc (group b.site)+(x-b.lo) else 0) ≠ 0
        rw [ite_eq_left h]
        omega
      simp [nz,h]
    · have z : (interval (BucketRows.row group acc b)).code g x = 0 := by
        unfold Interval.code
        split
        · rename_i covered
          exact (h covered).elim
        · rfl
      simp only [z,ite_true,ih,List.forall_mem_cons]
      tauto

private theorem source (group : I → ℕ) (acc : ℕ → ℕ) (bs : List (Bucket I)) (e : Interval)
    (he : e ∈ intervals group acc bs) :
    ∃ b ∈ bs, group b.site = e.group ∧ b.lo = e.first ∧ b.hi = e.stop := by
  induction bs generalizing acc with
  | nil => simp [intervals,BucketRows.pack] at he
  | cons b bs ih =>
    change e ∈ interval (BucketRows.row group acc b) :: intervals group (BucketRows.bump group acc b) bs at he
    obtain rfl | he := List.mem_cons.mp he
    · exact ⟨b,by simp,rfl,rfl,rfl⟩
    · obtain ⟨q,hq,hg,lo,hi⟩ := ih _ he
      exact ⟨q,List.mem_cons_of_mem _ hq,hg,lo,hi⟩

/-- Original buckets disjoint in their own group produce compatible decoded
rows independently of their order and their initial packed offsets. -/
theorem compatible (group : I → ℕ) (acc : ℕ → ℕ) (bs : List (Bucket I))
    (disj : bs.Pairwise (fun b c => group b.site = group c.site →
      ∀ x, b.lo ≤ x → x < b.hi → c.lo ≤ x → x < c.hi → False)) :
    (intervals group acc bs).Pairwise Compatible := by
  induction bs generalizing acc with
  | nil => simp [intervals,BucketRows.pack]
  | cons b bs ih =>
    change (interval (BucketRows.row group acc b) :: intervals group (BucketRows.bump group acc b) bs).Pairwise _
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp disj
    refine List.pairwise_cons.mpr ⟨?_,ih _ tail⟩
    intro e he hg x bx ex
    obtain ⟨c,hc,cg,cl,ch⟩ := source _ _ _ _ he
    exact head c hc (hg.trans cg.symm) x bx.1 bx.2 (cl.symm ▸ ex.1) (ch.symm ▸ ex.2)

/-- Even a bucket appearing in the middle of an unsorted descriptor list
has exactly its group's preceding total as its packed base address. -/
theorem code_middle (group : I → ℕ) (pre post : List (Bucket I)) (b : Bucket I) (x : ℕ)
    (disj : (intervals group (fun _ => 0) (pre++b::post)).Pairwise Compatible)
    (lo : b.lo ≤ x) (hi : x < b.hi) :
    pairCode (group b.site) x (intervals group (fun _ => 0) (pre++b::post)) =
      1 + BucketRows.count group pre (group b.site) + (x-b.lo) := by
  let e : Interval := ⟨group b.site,b.lo,b.hi,BucketRows.count group pre (group b.site)⟩
  have mem : e ∈ intervals group (fun _ => 0) (pre++b::post) := by
    simp [intervals,BucketRows.middle,interval,e]
  exact pairCode_owned _ _ disj mem rfl ⟨lo,hi⟩

theorem plan_rows {F : Type*} [CommSemiring F] {S : Shape} (P : Plan F S) (h : P.History)
    (group : (P.finish h).Site → ℕ) (bs : List (Bucket S.Site)) :
    (P.bucketRows h group bs).map interval =
      intervals (group ∘ P.destination h) (fun _ => 0) bs := rfl

end ThreeFlat.Diagonal.BucketIntervalCodes

end OAI
