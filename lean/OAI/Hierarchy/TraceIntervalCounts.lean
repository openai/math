import OAI.Hierarchy.FactorBucketInputs
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Computing native registration counts from clipped initial intervals -/

namespace Hierarchy.TraceAdmission

open FactorPinIntervals
open scoped BigOperators

/-- Intersection length of one initial bucket with the indicated half-open tape region. -/
def bandLength (span bucket lo hi : ℕ) :=
  bucketLength hi span bucket - bucketLength lo span bucket

theorem bucket_prefix (cap span n : ℕ) :
    ∑ q ∈ Finset.range n, bucketLength cap span q = min cap (n*span) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,Nat.succ_mul,bucketLength]
    omega

theorem bandLength_eq (span bucket lo hi : ℕ) (h : lo≤hi) :
    bandLength span bucket lo hi =
      min hi ((bucket+1)*span) - max lo (bucket*span) := by
  rw [bandLength,bucketLength,bucketLength,Nat.succ_mul]
  omega

private theorem prefix_mono (span q : ℕ) {lo hi : ℕ} (h : lo≤hi) :
    bucketLength lo span q ≤ bucketLength hi span q :=
  min_le_min_left _ (Nat.sub_le_sub_right h _)

/-- Taken across every initial interval, a direction costs exactly its number of
external pairs. Spans and band endpoints in this lemma are measured in pairs. -/
theorem sum_bandLength {lanes span lo hi : ℕ} (order : lo≤hi) (room : hi≤lanes*span) :
    (∑ q : Fin lanes, bandLength span q.val lo hi)=hi-lo := by
  have rejoin : ∑ q ∈ Finset.range lanes,
      (bandLength span q lo hi+bucketLength lo span q) = ∑ q ∈ Finset.range lanes,
        bucketLength hi span q := by
    apply Finset.sum_congr rfl
    intro q _
    exact Nat.sub_add_cancel (prefix_mono span q order)
  rw [Finset.sum_add_distrib,bucket_prefix,bucket_prefix,min_eq_left room,
    min_eq_left (order.trans room)] at rejoin
  rw [Fin.sum_univ_eq_sum_range (fun q=>bandLength span q lo hi) lanes]
  omega

/-- Sum over the actual immutable root destinations, without expanding any input bits. -/
def rootSum {lanes roots : ℕ} (dest : Fin lanes → Fin roots) (v : Fin roots)
    (weight : ℕ → ℕ) :=
  ∑ q : Fin lanes, if dest q=v then weight q.val else 0

theorem rootSum_lists {lanes roots : ℕ} (dest : Fin lanes → Fin roots) (v : Fin roots)
    (weight : ℕ → ℕ) :
    ((((List.finRange lanes).filter fun q => dest q=v).map fun q => weight q.val).sum =
      rootSum dest v weight) := by
  classical
  have split := List.sum_map_ite (fun q : Fin lanes => dest q=v)
    (fun q => weight q.val) (fun _ => 0) (List.finRange lanes)
  simpa [rootSum,List.finRange,List.map_ofFn,Function.comp_def,List.sum_ofFn] using split.symm

theorem total_rootSum {lanes roots : ℕ} (dest : Fin lanes → Fin roots) (weight : ℕ→ℕ) :
    (∑ v,rootSum dest v weight)=∑ q : Fin lanes,weight q.val := by
  classical
  unfold rootSum
  rw [Finset.sum_comm]
  simp

def inputCount {lanes roots : ℕ} (dest : Fin lanes → Fin roots) (v : Fin roots) (cap pairSpan : ℕ) :=
  rootSum dest v (bucketLength cap (2*pairSpan))

def directionCount {lanes roots : ℕ} (dest : Fin lanes → Fin roots) (v : Fin roots)
    (band pairSpan direction : ℕ) :=
  rootSum dest v (fun q => bandLength pairSpan q (direction*band) ((direction+1)*band))

theorem total_inputCount {lanes roots : ℕ} (dest : Fin lanes→Fin roots) (cap pairSpan : ℕ)
    (room : cap≤lanes*(2*pairSpan)) : (∑ v,inputCount dest v cap pairSpan)=cap := by
  unfold inputCount
  rw [total_rootSum,Fin.sum_univ_eq_sum_range (bucketLength cap (2*pairSpan)) lanes,bucket_prefix,min_eq_left room]

theorem total_directionCount {lanes roots : ℕ} (dest : Fin lanes→Fin roots) (band pairSpan i : ℕ)
    (room : (i+1)*band≤lanes*pairSpan) : (∑ v,directionCount dest v band pairSpan i)=band := by
  unfold directionCount
  rw [total_rootSum,sum_bandLength (Nat.mul_le_mul_right _ (Nat.le_succ i)) room,
    Nat.succ_mul,Nat.add_sub_cancel_left]


end Hierarchy.TraceAdmission

end OAI
