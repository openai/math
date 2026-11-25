import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Sign.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! The radix step in the proof of sign-preserving rounding (Appendix A). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open SignType

variable {ι : Type*}

/-- A signed-digit expansion, with the most significant digit first. -/
def radixDigits (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | d :: ds => B ^ ds.length * d + radixDigits B ds

/-- The sign of the first nonzero digit, including the all-zero case. -/
def leadingSign : List ℤ → SignType
  | [] => 0
  | d :: ds => if d = 0 then leadingSign ds else sign d

theorem abs_radixDigits_lt {B : ℤ} (hB : 0 < B) {ds : List ℤ}
    (hd : ∀ d ∈ ds, |d| < B) : |radixDigits B ds| < B ^ ds.length := by
  induction ds with
  | nil => simp [radixDigits]
  | cons d ds ih =>
    have hhead : |d| ≤ B - 1 := by have := hd d (by simp); omega
    have htail : |radixDigits B ds| < B ^ ds.length :=
      ih fun x hx => hd x (by simp [hx])
    have hp : 0 ≤ B ^ ds.length := pow_nonneg hB.le _
    calc
      |radixDigits B (d :: ds)| ≤ |B ^ ds.length * d| + |radixDigits B ds| :=
        abs_add_le _ _
      _ < B ^ ds.length * (B - 1) + B ^ ds.length := by
        rw [abs_mul, abs_of_nonneg hp]
        exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hhead hp) htail
      _ = B ^ (d :: ds).length := by simp [pow_succ]; ring

theorem sign_radixDigits {B : ℤ} (hB : 0 < B) {ds : List ℤ}
    (hd : ∀ d ∈ ds, |d| < B) : sign (radixDigits B ds) = leadingSign ds := by
  induction ds with
  | nil => simp [radixDigits, leadingSign]
  | cons d ds ih =>
    have ht : ∀ x ∈ ds, |x| < B := fun x hx => hd x (by simp [hx])
    have hr := abs_lt.mp (abs_radixDigits_lt hB ht)
    have hp := pow_pos hB ds.length
    rw [radixDigits, leadingSign]
    split_ifs with h
    · simpa [h] using ih ht
    · rcases lt_or_gt_of_ne h with hn | hn
      · have he : d ≤ -1 := by omega
        have hm := mul_le_mul_of_nonneg_left he hp.le
        rw [sign_neg hn, sign_neg (by linarith [hr.2] : B ^ ds.length * d + radixDigits B ds < 0)]
      · have he : 1 ≤ d := by omega
        have hm := mul_le_mul_of_nonneg_left he hp.le
        rw [sign_pos hn, sign_pos (by linarith [hr.1] : 0 < B ^ ds.length * d + radixDigits B ds)]

/-- Pack the short integer vectors produced by the successive projections. -/
def radixVector (B : ℤ) : List (ι → ℤ) → (ι → ℤ)
  | [] => 0
  | z :: zs => B ^ zs.length • z + radixVector B zs

theorem radixVector_apply (B : ℤ) (zs : List (ι → ℤ)) (i : ι) :
    radixVector B zs i = radixDigits B (zs.map (fun z => z i)) := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp [radixVector, radixDigits, ih, zsmul_eq_mul]

theorem dotProduct_radixVector [Fintype ι] (a : ι → ℤ) (B : ℤ) (zs : List (ι → ℤ)) :
    dotProduct a (radixVector B zs) = radixDigits B (zs.map (dotProduct a)) := by
  induction zs with
  | nil => simp [radixVector, radixDigits]
  | cons z zs ih =>
    simp only [radixVector, dotProduct_add, ih, List.map_cons, radixDigits, List.length_map]
    rw [dotProduct_smul]
    rfl

theorem abs_dotProduct_le [Fintype ι] (a z : ι → ℤ) {D : ℤ}
    (hz : ∀ i, |z i| ≤ D) : |dotProduct a z| ≤ (∑ i, |a i|) * D := by
  rw [dotProduct, Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hz i) (abs_nonneg _))

/-- For every allowed integer form, the sign of the packed vector is determined by its
first nonzero test on the constituent vectors. -/
theorem sign_dotProduct_radixVector [Fintype ι] {B M D : ℤ}
    (hB : 0 < B) (hD : 0 ≤ D) (hMD : M * D < B)
    (zs : List (ι → ℤ)) (hz : ∀ z ∈ zs, ∀ i, |z i| ≤ D)
    (a : ι → ℤ) (ha : ∑ i, |a i| ≤ M) :
    sign (dotProduct a (radixVector B zs)) = leadingSign (zs.map (dotProduct a)) := by
  rw [dotProduct_radixVector]
  apply sign_radixDigits hB
  intro n hn
  obtain ⟨z, hmem, rfl⟩ := List.mem_map.mp hn
  exact ((abs_dotProduct_le a z (hz z hmem)).trans
    (mul_le_mul_of_nonneg_right ha hD)).trans_lt hMD

theorem abs_radixVector_lt {B : ℤ} (hB : 0 < B) (zs : List (ι → ℤ))
    (hz : ∀ z ∈ zs, ∀ i, |z i| < B) (i : ι) : |radixVector B zs i| < B ^ zs.length := by
  rw [radixVector_apply]
  rw [← List.length_map (f := fun z : ι → ℤ => z i) (as := zs)]
  apply abs_radixDigits_lt hB
  intro d hd
  obtain ⟨z, hmem, rfl⟩ := List.mem_map.mp hd
  exact hz z hmem i

end Lattice
end LinearProgramming
end Optimization
end OAI
