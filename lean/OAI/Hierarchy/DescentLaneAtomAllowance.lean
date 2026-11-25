import OAI.Hierarchy.DescentGrainCalendar

namespace OAI
/-! # Absorbing all actual p-lane router births in one chronological slot allowance -/

namespace Hierarchy.DescentCompiler.AtomSchedule
variable (S : AtomSchedule)

/-- A calendar grain contains the terminal multiplier and at most one initial
bundle's worth of base-b digits. -/
theorem normalized_grain_le (b p age : ℕ) (hb : 0<b) :
    S.grainAt b p age*b ≤ p*b^(S.rounds*S.height+1) := by
  dsimp only [grainAt]
  rw [Nat.mul_assoc,←pow_succ]
  exact Nat.mul_le_mul_left p (Nat.pow_le_pow_right hb (Nat.succ_le_succ (Nat.sub_le _ _)))

/-- Price the geometric capacity growth and the remaining unscaled grain separately.
The physical terminal lane multiplier has already canceled from the node comparison. -/
theorem lane_room {i b logb physicalGain grain cap : ℕ} (height : 0<S.height)
    (age : i≤S.length) (branch : b≤2^logb) (grainBound : grain≤b^(S.rounds*S.height+1))
    (capacity : cap≤2^(8+physicalGain*i)) (gain : logb+physicalGain≤S.capGain) :
    2*grain*cap≤2^(11+S.capGain*S.length) := by
  have lengths : S.rounds*S.height+1≤S.length := by
    dsimp [length]
    rw [Nat.add_mul,one_mul]
    omega
  have expo : logb*(S.rounds*S.height+1)+physicalGain*i≤S.capGain*S.length := by
    apply le_trans (Nat.add_le_add (Nat.mul_le_mul_left logb lengths) (Nat.mul_le_mul_left physicalGain age))
    rw [←Nat.add_mul]
    exact Nat.mul_le_mul_right _ gain
  have raw := grainBound.trans (Nat.pow_le_pow_left branch _)
  calc
    _ ≤ (2^1*(2^logb)^(S.rounds*S.height+1))*2^(8+physicalGain*i) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 raw) capacity
    _ = 2^(1+logb*(S.rounds*S.height+1)+(8+physicalGain*i)) := by rw [←pow_mul,←pow_add,←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

theorem lane_batch {i b logb physicalGain grain cap : ℕ} (height : 0<S.height)
    (age : i≤S.length) (branch : b≤2^logb) (grainBound : grain≤b^(S.rounds*S.height+1))
    (capacity : cap≤2^(8+physicalGain*i)) (gain : logb+physicalGain≤S.capGain) :
    (S.hostSize i*(S.groupCount i*S.radix))*(2*grain*cap)≤S.batch :=
  Nat.mul_le_mul (S.slot_reserve age) (S.lane_room height age branch grainBound capacity gain)

/-- The corresponding bitwise bound carries its real multiplicative p, when a
caller selects individual-bit comparisons instead of p-bit operand descriptors. -/
theorem raw_lane_batch {i b logb physicalGain grain cap : ℕ} (p : ℕ) (height : 0<S.height)
    (age : i≤S.length) (branch : b≤2^logb) (grainBound : grain≤p*b^(S.rounds*S.height+1))
    (capacity : cap≤2^(8+physicalGain*i)) (gain : logb+physicalGain≤S.capGain) :
    (S.hostSize i*(S.groupCount i*S.radix))*(2*grain*cap)≤p*S.batch := by
  let width := b^(S.rounds*S.height+1)
  have normal := S.lane_batch height age branch (le_refl width) capacity gain
  calc
    _ ≤ (S.hostSize i*(S.groupCount i*S.radix))*(2*(p*width)*cap) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 grainBound))
    _ = p*((S.hostSize i*(S.groupCount i*S.radix))*(2*width*cap)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left p normal

end Hierarchy.DescentCompiler.AtomSchedule

end OAI
