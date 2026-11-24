import OAI.Computability.VPVNP.CutSchedule

/-!
# Computing the cut lengths from the distributed group index

The first-half group numbered `i` needs the two incident lengths and the
three lengths at its primed pair. Equation (9.1) lets the group compute
all five using the position of the highest set bit and the number of set
bits in its index, without storing the index in a RAM word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderWidths

/-- Two incident cuts and the three cuts of the primed pair. -/
inductive Slot where
  | liveLeft | liveRight | primedLeft | primedMiddle | primedRight
  deriving DecidableEq

/-- Convert a group number and width slot to the cut index used in the live or primed chain. -/
def index (i : ℕ) : Slot → ℕ
  | .liveLeft => i - 1
  | .liveRight => i
  | .primedLeft => 2*i - 2
  | .primedMiddle => 2*i - 1
  | .primedRight => 2*i

/-- Each block has `Δ` bits. Subtracting one from the group index crosses
a power of two precisely when the population count is one. -/
def blocks (H high count : ℕ) : Slot → ℕ
  | .liveLeft => if high = 0 then 0 else (H - high) + (if count = 1 then 1 else 0)
  | .liveRight => H - high
  | .primedLeft => if high = 0 then 0 else (H - high - 1) + (if count = 1 then 1 else 0)
  | .primedMiddle => (H - high - 1) + (if count = 1 then 1 else 0)
  | .primedRight => H - high - 1

theorem blocks_le (H high count : ℕ) (s : Slot) (hH : 0 < H) : blocks H high count s ≤ H := by
  cases s <;> simp only [blocks] <;> (try split_ifs) <;> omega

private theorem log_pred {i : ℕ} (hi : 1 < i) :
    Nat.log 2 (i - 1) =
      Nat.log 2 i - (if i = 2 ^ Nat.log 2 i then 1 else 0) := by
  have hlo := Nat.pow_log_le_self 2 (by omega : i ≠ 0)
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) i
  split_ifs with hp
  · have hk : Nat.log 2 i ≠ 0 := by
      intro hz
      rw [hz, pow_zero] at hp
      omega
    have he : Nat.log 2 i - 1 + 1 = Nat.log 2 i := by omega
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · have h := congrArg (fun k => 2^k) he
      rw [pow_succ, ← hp] at h
      have := Nat.two_pow_pos (Nat.log 2 i - 1)
      omega
    · rw [he, ← hp]
      omega
  · rw [Nat.sub_zero]
    apply Nat.log_eq_of_pow_le_of_lt_pow <;> omega

private theorem log_twice_pred {i : ℕ} (hi : 0 < i) :
    Nat.log 2 (2*i - 1) = Nat.log 2 i + 1 - (if i = 2 ^ Nat.log 2 i then 1 else 0) := by
  have hd : Nat.log 2 (2*i) = Nat.log 2 i + 1 := by
    rw [Nat.mul_comm, Nat.log_mul_base (by decide : 1 < 2) hi.ne']
  rw [log_pred (by omega : 1 < 2*i), hd, pow_succ]
  have hp : 2 * i = 2 ^ Nat.log 2 i * 2 ↔ i = 2 ^ Nat.log 2 i := by omega
  rw [if_congr hp rfl rfl]

/-- The number of set bits is needed only to distinguish powers of two.
The two clamped endpoints are covered, including the case of just one
first-half group. -/
theorem blocks_width (h Δ i count : ℕ) (s : Slot) (hi : 0 < i) (hle : i ≤ 2^h)
    (hc : count = 1 ↔ i = 2 ^ Nat.log 2 i) :
    blocks (h+1) (Nat.log 2 i) count s * Δ = CutSchedule.width (h+1) Δ (index i s) := by
  have hlt : i < 2^(h+1) := by rw [pow_succ]; omega
  have hk : Nat.log 2 i ≤ h := by
    simpa [Nat.log_pow (by decide : 1 < 2)] using Nat.log_mono_right (b := 2) hle
  have hz : Nat.log 2 i = 0 ↔ i = 1 := by
    rw [Nat.log_eq_zero_iff]; omega
  have hright : blocks (h+1) (Nat.log 2 i) count .liveRight * Δ =
      CutSchedule.width (h+1) Δ i := by simp [blocks, CutSchedule.width, hi, hlt]
  have hleft : blocks (h+1) (Nat.log 2 i) count .liveLeft * Δ =
      CutSchedule.width (h+1) Δ (i-1) := by
    by_cases he : i = 1
    · simp [blocks, he]
    · have hn := mt hz.mp he
      have hin : 0 < i-1 ∧ i-1 < 2^(h+1) := by omega
      rw [CutSchedule.width, ite_eq_left hin, log_pred (by omega), ← if_congr hc rfl rfl]
      simp only [blocks, ite_eq_right hn]
      congr 1
      split_ifs <;> omega
  cases s with
  | liveLeft => exact hleft
  | liveRight => exact hright
  | primedMiddle =>
    have hm : 0 < 2*i-1 ∧ 2*i-1 < 2^(h+1) := by rw [pow_succ]; omega
    rw [index, CutSchedule.width, ite_eq_left hm, log_twice_pred hi, ← if_congr hc rfl rfl, blocks]
    congr 1
    split_ifs <;> omega
  | primedRight =>
    have hd := CutSchedule.width_double h Δ i hi hle
    rw [← hright] at hd
    change (h+1-Nat.log 2 i)*Δ = _ at hd
    have hh : h+1-Nat.log 2 i = (h+1-Nat.log 2 i - 1) + 1 := by omega
    rw [hh, Nat.succ_mul] at hd
    exact Nat.add_right_cancel hd
  | primedLeft =>
    by_cases he : i = 1
    · simp [blocks, index, he]
    · have hn := mt hz.mp he
      have hd := CutSchedule.width_double h Δ (i-1) (by omega) (by omega)
      rw [← hleft] at hd
      simp only [blocks, ite_eq_right hn] at hd ⊢
      rw [index, show 2*i-2 = 2*(i-1) by omega]
      have hh : (h+1-Nat.log 2 i) + (if count = 1 then 1 else 0) =
          ((h+1-Nat.log 2 i - 1) + (if count = 1 then 1 else 0)) + 1 := by omega
      rw [hh, Nat.succ_mul] at hd
      exact Nat.add_right_cancel hd

/-- Slots actually used at a group. A tail group needs only its incident cuts. -/
def Needed (h i : ℕ) (s : Slot) : Prop := i ≤ 2^h ∨ s = .liveLeft ∨ s = .liveRight

/-- Correctness of every requested length throughout the chain, including
the final group, where the outgoing live width is clamped to zero. -/
theorem needed_width (h Δ i count : ℕ) (s : Slot) (hi : 0 < i) (hend : i ≤ 2^(h+1))
    (hc : count = 1 ↔ i = 2 ^ Nat.log 2 i) (hs : Needed h i s) :
    blocks (h+1) (Nat.log 2 i) count s * Δ = CutSchedule.width (h+1) Δ (index i s) := by
  by_cases hf : i ≤ 2^h
  · exact blocks_width h Δ i count s hi hf hc
  have hleft : CutSchedule.width (h+1) Δ (i-1) = Δ := CutSchedule.width_tail _ _ _ (by omega) (by omega)
  have hs' := hs.resolve_left hf
  by_cases he : i = 2^(h+1)
  · have hk : Nat.log 2 i = h+1 := he ▸ Nat.log_pow (by decide) _
    have hp : count = 1 := hc.mpr (hk ▸ he)
    rcases hs' with rfl | rfl
    · simp [blocks, index, hk, hp, hleft]
    · simp [blocks, index, he]
  · have hk : Nat.log 2 i = h := Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
    have hp : count ≠ 1 := by intro hh; have heq := hc.mp hh; rw [hk] at heq; omega
    have hh : h ≠ 0 := by rintro rfl; norm_num at *; omega
    have hright : CutSchedule.width (h+1) Δ i = Δ := CutSchedule.width_tail _ _ _ (by omega) (by omega)
    rcases hs' with rfl | rfl
    · simp [blocks, index, hk, hp, hh, hleft]
    · simp [blocks, index, hk, hright]

/-- The position and the population suffice to dispatch the two halves.
A group whose highest bit is at the halfway exponent belongs to the first
half precisely when that bit is its only set bit. -/
theorem firstHalf_iff (h i c : ℕ) (hi : 0 < i) (hc : c = 1 ↔ i = 2 ^ Nat.log 2 i) :
    Nat.log 2 i < h ∨ Nat.log 2 i = h ∧ c = 1 ↔ i ≤ 2^h := by
  rw [Nat.log_lt_iff_lt_pow (by decide) hi.ne', hc]
  constructor
  · rintro (hl | ⟨hk, he⟩)
    · exact hl.le
    · simpa [hk] using he.le
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | rfl
    · exact Or.inl hlt
    · simp [Nat.log_pow (by decide : 1 < 2)]

/-- Endpoint tests in the same small word representation. -/
theorem endpoints_iff (H i : ℕ) (hi : 0 < i) (hend : i ≤ 2^H) :
    (Nat.log 2 i = 0 ↔ i = 1) ∧ (Nat.log 2 i = H ↔ i = 2^H) := by
  constructor
  · rw [Nat.log_eq_zero_iff]; omega
  · constructor
    · intro hk
      have := Nat.pow_log_le_self 2 hi.ne'
      rw [hk] at this
      omega
    · rintro rfl
      exact Nat.log_pow (by decide) _

end LiveHeaderWidths

end VPVNP
end Computability
end OAI
