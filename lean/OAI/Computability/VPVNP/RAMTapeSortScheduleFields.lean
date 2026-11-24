import OAI.Computability.VPVNP.RAMSortCostLayout
import OAI.Computability.VPVNP.RAMTapeSuccessorFields

/-!
# Streaming the physical exchange blocks in stage order

Local strides leave the incident stream untouched. At every cross-site
stride its next two whole blocks are the outgoing and incoming fields for
that layer. Thus one forward pass over the stream implements the address
formula of Lemma 10.1 without storing a numerical global wire address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortSchedule

open RAMSort RAMLayout

/-- Physical layer number, present only for cross-site comparisons. -/
def exchangeNumber {b : ℕ} (h : ℕ) (s : Stage b) : Option ℕ :=
  if h ≤ s.stride then some (layerCount (s.phase-h-1) + (s.phase-s.stride-1)) else none

theorem exchangeNumber_eq {h d : ℕ} (s : Stage (h+d)) (hc : h ≤ s.stride) :
    exchangeNumber h s = some (((crossStageEquiv h d).symm ⟨s,hc⟩).ordinal.val) := by
  simp [exchangeNumber, hc, crossStageEquiv, Layer.ordinal]

private theorem strides_numbers {b : ℕ} (h a : ℕ) (ha : a ≤ b) (k : ℕ) (hk : k ≤ a) :
    (strides b a ha k hk).filterMap (exchangeNumber h) =
      List.range' (layerCount (a-h-1)+(a-k)) (k-h) := by
  induction k with
  | zero => simp [strides]
  | succ k ih =>
    rw [strides, List.filterMap_cons]
    by_cases hc : h ≤ k
    · have hcount : k+1-h = (k-h)+1 := by omega
      have hpos : layerCount (a-h-1)+(a-(k+1))+1 = layerCount (a-h-1)+(a-k) := by omega
      simp only [exchangeNumber, hc, ite_true, ih (by omega), hcount, List.range', hpos]
      congr 2
    · simp only [exchangeNumber, hc, ite_false, ih (by omega)]
      rw [show k-h=0 by omega, show k+1-h=0 by omega]
      rfl

private theorem phases_numbers {b : ℕ} (h a : ℕ) (ha : a ≤ b) :
    (phases b a ha).filterMap (exchangeNumber h) = List.range' 0 (layerCount (a-h)) := by
  induction a with
  | zero => simp [phases, layerCount]
  | succ a ih =>
    rw [phases, List.filterMap_append, ih, strides_numbers]
    simp only [Nat.sub_self, Nat.add_zero]
    by_cases hle : h ≤ a
    · have he : a+1-h=(a-h)+1 := by omega
      rw [he, Nat.add_sub_cancel]
      have ht (v : ℕ) : layerCount (v+1) = layerCount v + (v+1) := by
        rw [layerCount, layerCount, Nat.choose_succ_succ (v+1) 1, Nat.choose_one_right, Nat.add_comm]
      rw [ht]
      simpa only [Nat.zero_add] using
        (List.range'_append_1 (s := 0) (m := layerCount (a-h)) (n := a-h+1))
    · rw [show a+1-h=0 by omega, show a-h=0 by omega]
      rfl

/-- Reading two consecutive blocks per cross stride visits physical layer
ordinals from zero up to the full incident width, in exactly that order. -/
theorem exchangeNumbers (h d : ℕ) :
    (phases (h+d) (h+d) le_rfl).filterMap (exchangeNumber h) = List.range (layerCount d) := by
  simpa only [Nat.add_sub_cancel_left, List.range_eq_range'] using phases_numbers h (h+d) le_rfl

/-- Concatenating the blocks in execution order gives the same input stream
as iterating over their physical field indices. -/
theorem exchangeStream (h d : ℕ) (field : ℕ → List Bool) :
    ((phases (h+d) (h+d) le_rfl).filterMap (exchangeNumber h)).flatMap field =
      (List.range (layerCount d)).flatMap field := by rw [exchangeNumbers]


variable {d H w : ℕ}

/-- The two contiguous directions reserved for a physical layer ordinal. -/
def fieldPair (incident : Fin (width d H w) → Bool) (i : ℕ) : List Bool :=
  if hi : i < layerCount d then
    let layer := (layerEquiv d).symm ⟨i, hi⟩
    (List.ofFn fun j : Fin (blockBits H w) => incident (offset d H w (.inr (layer, 0, j)))) ++
      (List.ofFn fun j : Fin (blockBits H w) => incident (offset d H w (.inr (layer, 1, j))))
  else []

private theorem two_fields {n : ℕ} (f : Fin (2*n) → Bool) :
    List.ofFn f = (List.ofFn fun j : Fin n => f (finProdFinEquiv (0, j))) ++
      (List.ofFn fun j : Fin n => f (finProdFinEquiv (1, j))) := by
  rw [SuccessorFields.raw_eq_flatten]
  simp [List.ofFn_succ]

private theorem ordinal_map {α : Type*} (f : ℕ → α) (n : ℕ) :
    (List.ofFn fun i : Fin n => f i.val) = (List.range n).map f := by
  apply List.ext_getElem (by simp)
  intros
  simp

/-- The tape bytes consumed by the successor pass and by the chronological
stage loop are exactly the supplied incident bit vector, including for
arbitrary malformed record encodings. -/
theorem incident_stream (h : ℕ) (incident : Fin (width d H w) → Bool) :
    List.ofFn incident =
      (List.ofFn fun j : Fin (8*w) => incident (offset d H w (.inl (0,j)))) ++
      (List.ofFn fun j : Fin (8*w) => incident (offset d H w (.inl (1,j)))) ++
      ((phases (h+d) (h+d) le_rfl).filterMap (exchangeNumber h)).flatMap (fieldPair incident) := by
  rw [exchangeNumbers, List.flatMap_def, ← ordinal_map]
  apply (List.ofFn_add (n := 2*(8*w)) (m := layerCount d * (2*blockBits H w)) (f := incident)).trans
  congr 1
  · exact two_fields _
  · rw [SuccessorFields.raw_eq_flatten]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    rw [fieldPair, dite_eq_left i.isLt]
    have he : layerEquiv d ((layerEquiv d).symm i) = i := Equiv.apply_symm_apply _ _
    have pair (dir : Fin 2) (j : Fin (blockBits H w)) :
        offset d H w (.inr ((layerEquiv d).symm i, dir, j)) =
          Fin.natAdd (2*(8*w)) (finProdFinEquiv (i,finProdFinEquiv (dir,j))) := by
      change Fin.natAdd _ (finProdFinEquiv (layerEquiv d ((layerEquiv d).symm i), _)) = _
      rw [he]
    simpa only [pair] using
      (two_fields (fun j : Fin (2*blockBits H w) =>
        incident (Fin.natAdd (2*(8*w)) (finProdFinEquiv (i,j)))))

end RAMTape.SortSchedule

end VPVNP
end Computability
end OAI
