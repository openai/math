import OAI.ThreeFlat.Diagonal.HistoryContraction
import Mathlib.Data.List.GetD

namespace OAI
/-! # Canonical packed offsets of original bucket intervals

The table retains original bucket order. Its packed offset is the sum of
earlier interval lengths in the same scheduled group. Group membership
uses the complete chain of actual ownership maps along the chosen history.
-/

namespace ThreeFlat.Diagonal.HistoryContraction

structure Bucket (I : Type*) where
  site : I
  lo : ℕ
  hi : ℕ
  deriving DecidableEq

def Bucket.size {I : Type*} (b : Bucket I) := b.hi - b.lo

structure BucketRow (G : Type*) where
  group : G
  lo : ℕ
  hi : ℕ
  offset : ℕ
  deriving DecidableEq

namespace BucketRows

variable {I G : Type*} [DecidableEq G]

/-- The prefix accumulator update for one original bucket. -/
def bump (group : I → G) (acc : G → ℕ) (b : Bucket I) : G → ℕ :=
  Function.update acc (group b.site) (acc (group b.site) + b.size)

def row (group : I → G) (acc : G → ℕ) (b : Bucket I) : BucketRow G :=
  ⟨group b.site,b.lo,b.hi,acc (group b.site)⟩

def pack (group : I → G) (acc : G → ℕ) (bs : List (Bucket I)) : List (BucketRow G) :=
  match bs with
  | [] => []
  | b::rest => row group acc b :: pack group (bump group acc b) rest

def count (group : I → G) (bs : List (Bucket I)) (g : G) : ℕ :=
  (bs.map (fun b => if group b.site = g then b.size else 0)).sum

theorem fold_count (group : I → G) (bs : List (Bucket I)) (acc : G → ℕ) (g : G) :
    bs.foldl (bump group) acc g = acc g + count group bs g := by
  induction bs generalizing acc with
  | nil => simp [count]
  | cons b bs ih =>
    simp only [List.foldl_cons,ih,count,List.map_cons,List.sum_cons]
    by_cases h : group b.site = g
    · subst g; simp [bump,Nat.add_assoc]
    · simp [bump,Function.update_of_ne (Ne.symm h),h]

theorem pack_append (group : I → G) (xs ys : List (Bucket I)) (acc : G → ℕ) :
    pack group acc (xs++ys) = pack group acc xs ++ pack group (xs.foldl (bump group) acc) ys := by
  induction xs generalizing acc with
  | nil => rfl
  | cons b xs ih => simp [pack,ih]

/-- The only earlier buckets that contribute to this row are the ones already
owned by its scheduled group. -/
theorem middle (group : I → G) (xs : List (Bucket I)) (b : Bucket I) (ys : List (Bucket I)) :
    pack group (fun _ => 0) (xs ++ b::ys) =
      pack group (fun _ => 0) xs ++ ⟨group b.site,b.lo,b.hi,count group xs (group b.site)⟩ ::
        pack group (bump group (xs.foldl (bump group) (fun _ => 0)) b) ys := by
  rw [pack_append]
  simp [pack,row,fold_count]

theorem pack_length (group : I → G) (acc : G → ℕ) (bs : List (Bucket I)) :
    (pack group acc bs).length = bs.length := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih => simp [pack,ih]

end BucketRows

namespace Plan

variable {F : Type*} [CommSemiring F] {S : Shape} {G : Type*} [DecidableEq G]

/-- The forward owner at each stage can be read from its table independently
of the other buckets. The group is looked up once at the terminal site. -/
def bucketRows (P : Plan F S) (h : P.History) (group : (P.finish h).Site → G)
    (bs : List (Bucket S.Site)) : List (BucketRow G) :=
  BucketRows.pack (group ∘ P.destination h) (fun _ => 0) bs

end Plan
end ThreeFlat.Diagonal.HistoryContraction

end OAI
