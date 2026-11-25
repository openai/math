import OAI.ThreeFlat.Diagonal.MotifBinaryPacking
import OAI.ThreeFlat.Routing.TrackPackedData

namespace OAI
/-! # Stable compaction is literal binary concatenation of tile payloads

With the candidate slots in copy-major order, the live prefix is the word
used by the histogram port kernel. The result holds also for empty copies.
-/

namespace ThreeFlat.Diagonal.MotifBinaryPacking

open Routing Routing.StableCompaction
open scoped BigOperators

variable {r d : ℕ} (w : Fin r → ℕ) (fits : ∀ i, w i ≤ d)

private def widthBefore (i : ℕ) := ∑ j ∈ Finset.range i, if h : j < r then w ⟨j,h⟩ else 0

private theorem prefix_eq (i : Fin r) :
    (∑ j : Fin i.val, w (Fin.castLE i.isLt.le j)) = widthBefore w i.val := by
  rw [widthBefore, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [dite_eq_left (j.isLt.trans i.isLt)]
  rfl

private theorem prefix_lt {i i' : Fin r} (h : i < i') : widthBefore w i.val + w i ≤ widthBefore w i'.val := by
  have grow : widthBefore w (i.val+1) ≤ widthBefore w i'.val :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun _ _ _ => Nat.zero_le _)
  simpa only [widthBefore, Finset.sum_range_succ, dite_eq_left i.isLt] using grow

/-- Physical candidate slot of a packed payload bit. -/
def candidate (a : Fin (∑ i, w i)) : Fin (r*d) :=
  let x : (i : Fin r) × Fin (w i) := finSigmaFinEquiv.symm a
  finProdFinEquiv (x.1, Fin.castLE (fits x.1) x.2)

private theorem candidate_at (x : (i : Fin r) × Fin (w i)) :
    candidate w fits (finSigmaFinEquiv x) = finProdFinEquiv (x.1, Fin.castLE (fits x.1) x.2) := by
  let f (z : (i : Fin r) × Fin (w i)) := finProdFinEquiv (z.1, Fin.castLE (fits z.1) z.2)
  exact congrArg f (finSigmaFinEquiv.symm_apply_apply x)

private theorem candidate_mono : StrictMono (candidate w fits) := by
  intro a b ab
  obtain ⟨⟨i,j⟩,rfl⟩ := (finSigmaFinEquiv (n := w)).surjective a
  obtain ⟨⟨i',j'⟩,rfl⟩ := (finSigmaFinEquiv (n := w)).surjective b
  change (finSigmaFinEquiv (n := w) ⟨i,j⟩).val < (finSigmaFinEquiv (n := w) ⟨i',j'⟩).val at ab
  simp only [bit_offset, prefix_eq] at ab
  rw [candidate_at,candidate_at]
  change j.val + d*i.val < j'.val + d*i'.val
  rcases lt_trichotomy i i' with h|h|h
  · have hmul : d*(i.val+1) ≤ d*i'.val := Nat.mul_le_mul_left d h
    rw [Nat.mul_succ] at hmul
    have hj := j.isLt.trans_le (fits i)
    omega
  · subst i'; omega
  · have hh := prefix_lt w h
    have hj := j'.isLt
    omega

/-- The native compactor's packed bit stream is exactly the word in the
histogram kernel, for every choice of privately guessed tile selectors. -/
theorem stream_eq_flatten (x : (i : Fin r) → Fin (w i) → Bool) :
    TrackData.stream finProdFinEquiv.symm w fits x = flatten w x := by
  classical
  let M : Fin (r*d) → Bool := TrackData.mask finProdFinEquiv.symm w
  have hc : (active M).card = ∑ i, w i := TrackData.active_card _ w fits
  have live : ∀ a, candidate w fits a ∈ active M := by
    intro a
    obtain ⟨u,rfl⟩ := (finSigmaFinEquiv (n := w)).surjective a
    rw [candidate_at]
    simp [M,TrackData.mask,u.2.isLt]
  have ordered := Finset.orderEmbOfFin_unique hc live (candidate_mono w fits)
  funext a
  obtain ⟨⟨i,j⟩,rfl⟩ := (finSigmaFinEquiv (n := w)).surjective a
  let a : Fin (∑ i, w i) := finSigmaFinEquiv ⟨i,j⟩
  have ha : a.val < (active M).card := hc.symm ▸ a.isLt
  change compact M (TrackData.padded finProdFinEquiv.symm w x) (Fin.castLE _ a) = flatten w x a
  simp only [compact,Fin.val_castLE, dite_eq_left ha]
  have emb : (active M).orderEmbOfFin rfl ⟨a.val, ha⟩ = candidate w fits a := by
    rw [ordered]
    exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl
  rw [emb, candidate_at]
  let atPair (z : Fin r × Fin d) := if hz : z.2.val < w z.1 then x z.1 ⟨z.2.val,hz⟩ else false
  change atPair (finProdFinEquiv.symm (finProdFinEquiv (i,Fin.castLE (fits i) j))) = _
  rw [Equiv.symm_apply_apply]
  change (if hj : j.val < w i then x i ⟨j.val,hj⟩ else false) = _
  rw [dite_eq_left j.isLt]
  let f (z : (i : Fin r) × Fin (w i)) := x z.1 z.2
  exact (congrArg f (finSigmaFinEquiv.symm_apply_apply ⟨i,j⟩)).symm

end ThreeFlat.Diagonal.MotifBinaryPacking

end OAI
