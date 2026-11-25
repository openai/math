import OAI.ThreeFlat.Diagonal.SlotEnergy
import OAI.Computability.BorderVNP.PackedCellSlabs

namespace OAI
/-! # Consecutive intervals for the integer slot split -/

namespace ThreeFlat.Diagonal.SlotEnergy

open Computability.BorderVNP.Packing.CellSlabs

private def slotIndex (m : ℕ) : Fin m ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩

private theorem sum_initial (m n v : ℕ) (hn : n < m) :
    (∑ j : Fin m, if j.val < n then v else 0) = n * v := by
  let i : Fin m := ⟨n,hn⟩
  have hh : Finset.univ.filter (fun j : Fin m => j.val < n) = Finset.Iio i := by
    ext j
    simp [i, Fin.lt_def]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hh, Fin.card_Iio]
  rfl

/-- The offset is computed from the quotient and remainder in constant
arithmetic work, regardless of the number of parallel slots. -/
theorem start_piece (b m : ℕ) (i : Fin m) :
    start (slotIndex m) (piece b m) i = i.val * (b / m) + min i.val (b % m) := by
  have entry (j : Fin m) :
      (if (slotIndex m) j < (slotIndex m) i then piece b m j else 0) =
        (if j.val < i.val then b/m else 0) + (if j.val < min i.val (b%m) then 1 else 0) := by
    by_cases hj : j.val < i.val <;> by_cases hr : j.val < b%m <;>
      simp [piece, slotIndex, lt_min_iff, hj, hr]
  simp only [start, entry, Finset.sum_add_distrib,
    sum_initial m i.val (b/m) i.isLt,
    sum_initial m (min i.val (b%m)) 1 (lt_of_le_of_lt (min_le_left _ _) i.isLt), mul_one]

/-- A physical slot bit indexes the corresponding position of the whole
payload. Every bit occurs exactly once. -/
noncomputable def pieceIndex (b m : ℕ) (hm : 0 < m) :
    (Σ i, Fin (piece b m i)) ≃ Fin b :=
  (ordinal (slotIndex m) (piece b m)).trans (finCongr (sum_piece b m hm))

@[simp] theorem pieceIndex_val (b m : ℕ) (hm : 0 < m) (i : Fin m) (k : Fin (piece b m i)) :
    (pieceIndex b m hm ⟨i,k⟩).val = i.val*(b/m) + min i.val (b%m) + k.val := by
  change start (slotIndex m) (piece b m) i + k.val = _
  rw [start_piece]

/-- Replacing one binary equality by ties on the consecutive pieces
retains exactly the original equality. -/
theorem piece_equal_iff (b m : ℕ) (hm : 0 < m) (x y : Fin b → Bool) :
    (∀ i k, x (pieceIndex b m hm ⟨i,k⟩) = y (pieceIndex b m hm ⟨i,k⟩)) ↔ x = y := by
  constructor
  · intro h
    funext j
    obtain ⟨⟨i,k⟩,rfl⟩ := (pieceIndex b m hm).surjective j
    exact h i k
  · intro h i k
    rw [h]

end ThreeFlat.Diagonal.SlotEnergy

end OAI
