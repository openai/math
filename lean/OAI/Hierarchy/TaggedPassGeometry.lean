import OAI.Hierarchy.TaggedRadixPack
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI
/-! # Fixed slot counts and the two physical call heights of a digit pass -/

namespace Hierarchy.Tagged.Radix

structure PassShape where
  digitBits : ℕ
  packBits : ℕ
  rows : ℕ

def PassShape.block (s : PassShape) := 2^(2*s.digitBits)
def PassShape.pack (s : PassShape) := 2^s.packBits
def PassShape.perBlock (s : PassShape) := s.block + (2^s.digitBits+1)*s.pack
def PassShape.blocks (s : PassShape) := packCount s.block s.rows
def PassShape.nextRows (s : PassShape) := s.blocks*s.perBlock
def PassShape.packs (s : PassShape) := s.nextRows/s.pack
def PassShape.globalHeight (s : PassShape) := Nat.clog 2 s.packs

@[simp] theorem PassShape.next_eq (s : PassShape) : s.nextRows =
    passSlots s.block (2^s.digitBits+1) s.pack s.rows := rfl

theorem PassShape.real_fit (s : PassShape) : s.rows ≤ s.blocks*s.block := by
  simpa [blocks, Nat.mul_comm] using (pack_capacity s.block s.rows (by simp [block])).1

theorem PassShape.rows_le (s : PassShape) : s.rows ≤ s.nextRows :=
  s.real_fit.trans (Nat.mul_le_mul_left s.blocks (Nat.le_add_right ..))

theorem PassShape.local_height (s : PassShape) (space : s.packBits+2 ≤ s.digitBits) :
    s.perBlock ≤ 2^(2*s.digitBits+1) := by
  have kpos := Nat.two_pow_pos s.digitBits
  have digit : 2^s.digitBits+1 ≤ 2^(s.digitBits+1) := by rw [pow_succ]; omega
  have e : s.digitBits+1+s.packBits ≤ 2*s.digitBits := by omega
  have allowance : (2^s.digitBits+1)*s.pack ≤ s.block := calc
    _ ≤ 2^(s.digitBits+1)*2^s.packBits := Nat.mul_le_mul_right _ digit
    _ = 2^(s.digitBits+1+s.packBits) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) e
  change s.block + _ ≤ _
  rw [pow_succ]
  change s.block + _ ≤ s.block*2
  omega

theorem PassShape.pack_dvd (s : PassShape) (room : s.packBits ≤ 2*s.digitBits) : s.pack ∣ s.nextRows := by
  have a : s.pack ∣ s.block := pow_dvd_pow _ room
  have b : s.pack ∣ s.perBlock := dvd_add a (dvd_mul_left ..)
  exact dvd_mul_of_dvd_right b s.blocks

theorem PassShape.exact_packs (s : PassShape) (room : s.packBits ≤ 2*s.digitBits) :
    s.packs*s.pack = s.nextRows := Nat.div_mul_cancel (s.pack_dvd room)

private theorem pow_clog_double (n : ℕ) (hn : 0<n) : 2^Nat.clog 2 n ≤ 2*n := by
  by_cases one : n = 1
  · simp [one]
  · have p := Nat.pow_pred_clog_lt_self (by norm_num : 1<2) (show 1<n by omega)
    have h := Nat.clog_pos (by norm_num : 1<2) (show 1<n by omega)
    change 2^(Nat.clog 2 n-1)<n at p
    rw [show Nat.clog 2 n = (Nat.clog 2 n-1)+1 by omega, pow_succ]
    omega

theorem PassShape.local_volume (s : PassShape) : s.blocks*2^(2*s.digitBits+1) ≤ 2*s.nextRows := by
  rw [pow_succ, ← Nat.mul_assoc]
  change s.blocks*s.block*2 ≤ _
  have h : s.blocks*s.block ≤ s.nextRows := Nat.mul_le_mul_left _ (Nat.le_add_right ..)
  omega

theorem PassShape.global_volume (s : PassShape) (room : s.packBits ≤ 2*s.digitBits) (positive : 0<s.rows) :
    s.nextRows ≤ 2^s.globalHeight*s.pack ∧ 2^s.globalHeight*s.pack ≤ 2*s.nextRows := by
  have exactP := s.exact_packs room
  have pos : 0 < s.packs := by
    by_contra! z
    have eq := Nat.eq_zero_of_le_zero z
    have h := s.rows_le
    rw [eq, Nat.zero_mul] at exactP
    omega
  have lower := Nat.mul_le_mul_right s.pack (Nat.le_pow_clog (by norm_num : 1<2) s.packs)
  have upper := Nat.mul_le_mul_right s.pack (pow_clog_double s.packs pos)
  rw [Nat.mul_assoc,exactP] at upper
  exact ⟨exactP ▸ lower,upper⟩

theorem PassShape.global_height (s : PassShape) {h : ℕ} (room : s.packBits ≤ 2*s.digitBits)
    (inRoom : s.packBits ≤ h) (lower : 2^h ≤ s.nextRows) (upper : s.nextRows ≤ 4*2^h) :
    h-s.packBits ≤ s.globalHeight ∧ s.globalHeight ≤ h-s.packBits+2 := by
  have p := s.exact_packs room
  have low : 2^h ≤ 2^s.globalHeight*2^s.packBits := by
    apply lower.trans
    rw [← p]
    exact Nat.mul_le_mul_right _ (Nat.le_pow_clog (by norm_num : 1<2) _)
  rw [← pow_add] at low
  have lo := (Nat.pow_le_pow_iff_right (by norm_num : 1<2)).mp low
  refine ⟨by omega, Nat.clog_le_of_le_pow ?_⟩
  apply Nat.le_of_mul_le_mul_right (c := s.pack) ?_ (Nat.two_pow_pos _)
  rw [p]
  apply upper.trans
  change 4*2^h ≤ 2^(h-s.packBits+2)*2^s.packBits
  rw [←pow_add, show h-s.packBits+2+s.packBits = h+2 by omega,pow_add]
  omega

def slotSequence (seed k j : ℕ) : ℕ → ℕ
  | 0 => seed
  | i+1 => (PassShape.mk k j (slotSequence seed k j i)).nextRows

theorem slotSequence_bounds {h k j q passes : ℕ} (count : passes ≤ 2^q)
    (room : q+j+3 ≤ k) (endRoom : q+2*k+2 ≤ h+1) (i : ℕ) (hi : i ≤ passes) :
    2^(h+1) ≤ slotSequence (2^(h+1)) k j i ∧ slotSequence (2^(h+1)) k j i ≤ 2*2^(h+1) := by
  constructor
  · induction i with
    | zero => rfl
    | succ i ih => exact (ih (by omega)).trans (PassShape.rows_le ⟨k,j,slotSequence (2^(h+1)) k j i⟩)
  · apply passes_stay_linear (2^(2*k)) (2^k+1) (2^j) (2^(h+1)) passes
      (by positivity) (slotSequence (2^(h+1)) k j) le_rfl (fun _ _ => le_rfl) _ i hi
    exact dyadic_room (h+1) k j q passes count room endRoom

end Hierarchy.Tagged.Radix

end OAI
