import OAI.Computability.NearSquareRoot.CRTTableCoefficients

/-! # CRT coefficients within a consecutive block

A node of the balanced routing tree can generate its coefficients from its own
moduli. The modular fold for a column uses exactly the same interval of radices
as the fold for its global column, hence the two bounded inverses coincide.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication.Code

private theorem window_slice {α : Type*} (l : List α) {k b i j : ℕ} (hi : i ≤ b) :
    ((((l.drop k).take b).take i).drop j) = (l.take (k + i)).drop (k + j) := by
  rw [List.take_take, min_eq_left hi, List.take_drop, List.drop_drop]

/-- Row and column positions are local on the left and absolute on the right. -/
theorem coefficientAt_interval (axes : List Tally)
    (hcop : (axes.map List.length).Pairwise Nat.Coprime)
    (k b : ℕ) {i j : ℕ} (hrow : i < b) (hi : k + i < axes.length)
    (hj : j < i) (hm : 0 < axes[k + i].length) :
    coefficientAt ((axes.drop k).take b) i j = coefficientAt axes (k + i) (k + j) := by
  let block := (axes.drop k).take b
  have hlocal : i < block.length := by
    simp only [block, List.length_take, List.length_drop]
    omega
  have hmod : block[i].length = axes[k + i].length := by
    simp [block]
  have hc : (block.map List.length).Pairwise Nat.Coprime := by
    simpa only [block, List.map_take, List.map_drop] using hcop.drop.take
  have h := coefficientAt_window block hc hlocal hj (hmod ▸ hm)
  have g := coefficientAt_window axes hcop hi (Nat.add_lt_add_left hj k) hm
  rw [hmod] at h
  have he : (((block.map List.length).take i).drop j) =
      (((axes.map List.length).take (k+i)).drop (k+j)) := by
    rw [show block.map List.length = ((axes.map List.length).drop k).take b by
      simp [block]]
    exact window_slice _ hrow.le
  rw [he] at h
  have hunit : ((((axes.map List.length).take (k+i)).drop (k+j)).prod).Coprime axes[k+i].length :=
    Nat.coprime_of_mul_modEq_one (coefficientAt axes (k+i) (k+j)) (by rw [Nat.mul_comm]; exact g.2)
  exact (Nat.ModEq.cancel_right_of_coprime hunit.symm (h.2.trans g.2.symm)).eq_of_lt_of_lt h.1 g.1

/-- For serialized axes sliced at a node of width `b`, the decoded coefficient
still uses the global place-value weight of the target axis. -/
theorem coefficientAt_interval_weight {d : ℕ} (a : Fin d → ℕ)
    (hcop : Pairwise (fun i j => (a i).Coprime (a j))) (k b : ℕ) {i j : ℕ}
    (hrow : i < b) (hi : k + i < d) (hj : j < i) (hm : 0 < a ⟨k + i, hi⟩) :
    (coefficientAt (((List.ofFn (fun t => tally (a t))).drop k).take b) i j :
        ZMod (a ⟨k + i, hi⟩)) =
      CRT.weight a ⟨k + i, hi⟩ * (CRT.«prefix» a ⟨k + j, by omega⟩ : ZMod (a ⟨k + i, hi⟩)) := by
  let axes := List.ofFn (fun t => tally (a t))
  have ha : axes.map List.length = List.ofFn a := by simp [axes, Function.comp_def]
  have hc : (axes.map List.length).Pairwise Nat.Coprime := by
    rw [ha, List.pairwise_iff_getElem]
    intro s t hs ht hst
    simp only [List.getElem_ofFn]
    apply hcop
    exact fun e => hst.ne (congrArg Fin.val e)
  have hlen : k + i < axes.length := by simpa [axes] using hi
  have hpos : 0 < axes[k + i].length := by simpa [axes] using hm
  rw [coefficientAt_interval axes hc k b hrow hlen hj hpos]
  exact coefficientAt_weight a hcop (i := ⟨k + i, hi⟩) (j := ⟨k + j, by omega⟩)
    (show k + j < k + i by omega) hm

end CRTTable

end NearSquareRoot
end Computability
end OAI
