import OAI.Computability.NearSquareRoot.SynchronizedBoxLayout
import OAI.Computability.NearSquareRoot.SynchronizedBlockFourier
import OAI.Computability.NearSquareRoot.CoprimeBox

/-! # Synchronized short transforms on the actual integer multiplication box

On a valid box of at least four axes, the padded cyclic Fourier operator and
its adjoint each have exactly the three global layer shapes of the manuscript.
For the box constructed by trial division, their depth is bounded by an
absolute constant times one plus the binary logarithm of the address width.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedPadding SynchronizedBlocks

noncomputable section

variable {d : ℕ} {A : Fin d → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
variable {S : Fin (d/4) → Type} [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)]

private theorem flattened_schedule (hd : 4 ≤ d) (bits : ∀ j, BlockAddress A j ≃ Fin 2 × S j)
    (M : ∀ i, Matrix (A i) (A i) ℂ) (budget : ℕ)
    (hword : ∀ j : Fin (d/4), HasShortWord
      (tensorMatrix (fun i : Fin (count j) => M (axis j i))) budget) :
    ∃ w : List (Matrix (∀ i, A i) (∀ i, A i) ℂ),
      w.prod = tensorMatrix M ∧ (∀ N ∈ w, BoxStage hd bits N) ∧ w.length = 24 * budget := by
  let e := regroup hd A
  let relabel := reindexRingEquiv ℂ e.symm
  obtain ⟨w, hw, hstage, hlen⟩ := global_schedule bits _ budget hword
  refine ⟨w.map relabel, ?_, ?_, by simpa using hlen⟩
  · rw [← map_list_prod, hw]
    exact regroup_tensor hd M
  · intro N hN
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hN
    exact ⟨L, hstage _ hL, rfl⟩

/-- Matrix acting on the entire physical padded residue box. -/
def paddedFourier (box : List (ℕ × ℕ)) [∀ i, NeZero (BoxFin.modulus box i)] :
    Matrix (∀ i, BoxAxis box i) (∀ i, BoxAxis box i) ℂ :=
  tensorMatrix fun i => axisPadding (b := Fin (BoxFin.padding box i)) (ResidueFourier.axisMatrix (BoxFin.modulus box i))

set_option maxHeartbeats 1200000 in
/-- The concrete depth statement for both directions of the transform. Each
block contains at most seven axes and admits the same three global slot kinds. -/
theorem valid_box_word_with_layout {k L : ℕ} {box : List (ℕ × ℕ)} (h : BoxShape.Valid k L box)
    [∀ i, NeZero (BoxFin.modulus box i)] (hd : 4 ≤ box.length)
    {T : Fin (box.length/4) → Type} [∀ j, Fintype (T j)] [∀ j, DecidableEq (T j)]
    (bits : ∀ j, BlockAddress (BoxAxis box) j ≃ Fin 2 × T j) (inverse : Bool) :
    ∃ w : List (Matrix (∀ i, BoxAxis box i) (∀ i, BoxAxis box i) ℂ),
      w.prod = (if inverse then (paddedFourier box)ᴴ else paddedFourier box) ∧
      (∀ N ∈ w, BoxStage hd bits N) ∧ w.length = 7560000 * (L+2) := by
  let a := BoxFin.modulus box
  let c := BoxFin.padding box
  let width (i : Fin box.length) := (box.get i).1
  let U (i : Fin box.length) := axisPadding (b := Fin (c i)) (ResidueFourier.axisMatrix (a i))
  have localWord := blockFourier_word (L := L) a c width hd
    (fun i => (h.axisBounds _ (List.get_mem box i)).1)
    (fun i => (h.axisBounds _ (List.get_mem box i)).2.1)
    (fun i => Nat.add_sub_of_le (h.axisBounds _ (List.get_mem box i)).2.2.2)
  have hlen : 24 * (315000 * (L+2)) = 7560000 * (L+2) := by ring
  cases inverse with
  | false =>
    change ∃ w : List (Matrix (∀ i, BoxAxis box i) (∀ i, BoxAxis box i) ℂ), w.prod = tensorMatrix U ∧ (∀ N ∈ w, BoxStage hd bits N) ∧ w.length = _
    rw [← hlen]
    exact flattened_schedule hd bits U _ localWord
  | true =>
    have hlocal (j : Fin (box.length/4)) : HasShortWord
        (tensorMatrix fun i : Fin (count j) => (U (axis j i))ᴴ) (315000*(L+2)) := by
      rw [← tensorMatrix_conjTranspose]
      exact (localWord j).adjoint
    change ∃ w : List (Matrix (∀ i, BoxAxis box i) (∀ i, BoxAxis box i) ℂ), w.prod = (tensorMatrix U)ᴴ ∧ (∀ N ∈ w, BoxStage hd bits N) ∧ w.length = _
    rw [← hlen, tensorMatrix_conjTranspose]
    exact flattened_schedule hd bits (fun i => (U i)ᴴ) _ hlocal

/-- Applied to the executable coprime-box construction, the word bound has
logarithmic depth and each block pass uses at most one of its address bits. -/
theorem eventually_box_word :
    ∃ K : ℕ, ∀ k ≥ K, ∃ (h : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k))
      (hd : 4 ≤ (CoprimeBox.box k).length),
      let box := CoprimeBox.box k
      letI : ∀ i, NeZero (BoxFin.modulus box i) := BoxFin.modulus_neZero h
      ∀ inverse : Bool, ∃ w : List (Matrix (∀ i, BoxAxis box i) (∀ i, BoxAxis box i) ℂ),
        w.prod = (if inverse then (paddedFourier box)ᴴ else paddedFourier box) ∧
        (∀ N ∈ w, BoxStage hd (boxBits h) N) ∧ w.length = 7560000 * (20 * Nat.clog 2 k + 2) := by
  obtain ⟨K, hK⟩ := CoprimeBox.eventually_valid
  refine ⟨max K 1024, fun k hk => ?_⟩
  have h := hK k ((le_max_left ..).trans hk)
  have hd := four_le_length h (three_width_lt ((le_max_right ..).trans hk))
  let _ := BoxFin.modulus_neZero h
  exact ⟨h, hd, fun inverse => valid_box_word_with_layout h hd (boxBits h) inverse⟩

end

end ShortFourier

end NearSquareRoot
end Computability
end OAI
