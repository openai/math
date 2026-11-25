import OAI.Geometry.Hirsch.Normalization
import OAI.Geometry.Hirsch.Completion

noncomputable section

open Set Module

namespace OAI.Geometry.Hirsch

variable {Coord Row : Type}

def mask (usable : Set Coord) (vec : Vec Coord) : supported usable := by
  classical
  exact ⟨fun idx => if idx ∈ usable then vec idx else 0, fun idx hh => by simp [hh]⟩

namespace Blocking

variable (block : Blocking Coord Row)

def weight (row : Row) (idx : Coord) : ℝ := by
  classical
  exact block.coeff row (Pi.single idx 1)

theorem weight_nonneg (row : Row) (idx : Coord) : 0 ≤ block.weight row idx := by
  classical
  unfold weight
  rw [← map_zero (block.coeff row)]
  apply block.monotone
  intro other
  simp [Pi.single_apply]; split <;> norm_num

theorem weight_pos {row : Row} {idx : Coord} (hi : idx ∈ block.support row) :
    0 < block.weight row idx := lt_of_le_of_ne (block.weight_nonneg row idx) (Ne.symm hi)

theorem support_proj {row : Row} {idx : Coord} {scale : ℝ} (hs : scale ≠ 0)
    (he : block.coeff row = scale • LinearMap.proj idx) : block.support row = {idx} := by
  classical
  ext other
  simp [support, he, hs, Pi.single_apply, eq_comm]

variable [Fintype Coord]

theorem expand (row : Row) (vec : Vec Coord) :
    block.coeff row vec = ∑ idx, block.weight row idx * vec idx := by
  classical
  nth_rw 1 [← Finset.univ_sum_single vec]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro idx _
  rw [show Pi.single idx (vec idx) = vec idx • (Pi.single idx 1 : Vec Coord) by
    rw [← Pi.single_smul]; simp, map_smul, smul_eq_mul, mul_comm]
  rfl

theorem local_eq (row : Row) {first last : Vec Coord} (hh : EqOn first last (block.support row)) :
    block.coeff row first = block.coeff row last := by
  rw [block.expand row first, block.expand row last]
  apply Finset.sum_congr rfl
  intro idx _
  by_cases hi : idx ∈ block.support row
  · rw [hh hi]
  · have he : block.weight row idx = 0 := not_ne_iff.mp hi
    rw [he, zero_mul, zero_mul]

theorem coeff_mask (row : Row) (vec : Vec Coord) {usable : Set Coord}
    (hh : block.support row ⊆ usable) : block.coeff row (mask usable vec).val = block.coeff row vec := by
  apply block.local_eq
  intro idx hi
  simp [mask, hh hi]

def retained (usable : Set Coord) : Set Row := {row | block.support row ⊆ usable}

def restriction (usable : Set Coord) (rhs : Row → ℝ) :
    System (supported usable) (block.retained usable) where
  normal row := (block.coeff row).domRestrict (supported usable)
  rhs row := rhs row

omit [Fintype Coord] in
theorem pointed (usable : Set Coord) (rhs : Row → ℝ) :
    (block.restriction usable rhs).directions univ = ⊥ := by
  apply le_bot_iff.mp
  intro dir hd
  change dir = 0
  ext idx
  by_cases hi : idx ∈ usable
  · obtain ⟨row, scale, hs, he⟩ := block.individual idx
    have hr : row ∈ block.retained usable := by
      change block.support row ⊆ usable
      rw [block.support_proj hs.ne' he]
      exact singleton_subset_iff.mpr hi
    have hz := (System.mem_directions _).mp hd ⟨row, hr⟩ (mem_univ _)
    change block.coeff row dir.val = 0 at hz
    rw [he] at hz
    exact (mul_eq_zero.mp hz).resolve_left hs.ne'
  · exact dir.property idx hi

theorem perturb_restriction {pt : Timed Coord} {tol : ℝ} (ht : 0 < tol)
    (usable : Set Coord) (selected : Set Row)
    (hf : ∀ row, -tol < block.slack row pt)
    (hs : ∀ row ∈ selected, block.slack row pt < tol) :
    ∃ rhs, (∀ row, |rhs row - (block.slice pt.1).rhs row| < tol) ∧
      mask usable pt.2 ∈ (block.restriction usable rhs).body ∧
      ∀ row : block.retained usable, row.val ∈ selected →
        row ∈ (block.restriction usable rhs).active (mask usable pt.2) := by
  classical
  let rhs := fun row => if row ∈ selected ∨ block.slack row pt < 0
    then block.coeff row pt.2 else (block.slice pt.1).rhs row
  refine ⟨rhs, ?_, ?_, ?_⟩
  · intro row
    unfold rhs
    split
    · rename_i hh
      exact abs_lt.mpr ⟨hf row, hh.elim (hs row) (fun hn => hn.trans ht)⟩
    · simpa using ht
  · intro row
    change rhs row.val ≤ block.coeff row.val (mask usable pt.2).val
    rw [block.coeff_mask _ _ row.property]
    unfold rhs
    split
    · exact le_rfl
    · rename_i hh
      exact sub_nonneg.mp (le_of_not_gt (fun hn => hh (Or.inr hn)))
  · intro row hr
    change block.coeff row.val (mask usable pt.2).val = rhs row.val
    rw [block.coeff_mask _ _ row.property]
    simp [rhs, hr]

end Blocking
end OAI.Geometry.Hirsch
