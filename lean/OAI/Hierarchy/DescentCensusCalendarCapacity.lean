import OAI.Hierarchy.DescentCensusPrecision
import OAI.Hierarchy.DescentPrimitivePaletteCounts
import OAI.Hierarchy.DescentStateBounds

namespace OAI
/-! # Capacity and word precision of the census on a reached date -/

namespace Hierarchy.DescentCompiler.AtomSchedule
variable (S : AtomSchedule)

theorem local_capacity {i cap : ℕ} (hj : 0<S.height) (age : i≤S.length)
    (budget : cap≤2^(8+S.capGain*i)) : cap≤S.epochPower^S.localCapacityExponent := by
  apply budget.trans
  unfold epochPower localCapacityExponent
  rw [←pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  have h:=Nat.mul_le_mul_left S.capGain age
  have t : 8≤S.height*8 := by omega
  rw [length] at h
  rw [Nat.mul_add]
  simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using Nat.add_le_add t h

theorem grain_le_first (b p i : ℕ) (hb : 0<b) : S.grainAt b p i*b≤S.firstWidth b p := by
  unfold firstWidth grainAt
  simp only [ordinaryDone,Nat.zero_div,Nat.sub_zero]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (Nat.sub_le _ _)))

end Hierarchy.DescentCompiler.AtomSchedule

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler
open scoped Classical
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
  {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (S : AtomSchedule)
theorem census_caps_at {p grainAge : ℕ} (ready : A.StateBounds S i) (height : 0<S.height)
    (age : i≤S.length) (grain : A.z=S.grainAt G.b p grainAge)
    (wire : A.wire=S.epochPower^S.priceExponent) (base : G.b≤2^S.capGain) :
    2*A.cap≤S.censusCapacity ∧ A.wire*(A.z*G.b)*A.cap<2^(S.censusBits p) := by
  have charge:=S.local_capacity height age ready.capacity
  have units : A.z*G.b≤p*S.epochPower^S.localGrainExponent := by
    rw [grain]
    exact (S.grain_le_first _ _ _ G.base_pos).trans (S.first_width_payload height base p)
  constructor
  · exact Nat.mul_le_mul_left 2 charge
  rw [wire]
  have pp : p<2^(Nat.clog 2 (p+1)) := (Nat.lt_succ_self p).trans_le (Nat.le_pow_clog (by decide) _)
  calc
    _ ≤ S.epochPower^S.priceExponent*(p*S.epochPower^S.localGrainExponent)*S.epochPower^S.localCapacityExponent :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ units) charge
    _ = p*S.epochPower^S.censusExponent := by unfold AtomSchedule.censusExponent;rw [pow_add,pow_add];ring
    _ < 2^(Nat.clog 2 (p+1))*S.epochPower^S.censusExponent :=
      Nat.mul_lt_mul_of_pos_right pp (pow_pos (Nat.two_pow_pos _) _)
    _ = 2^(S.censusBits p) := by unfold AtomSchedule.censusBits AtomSchedule.epochPower;rw [pow_add,pow_mul]

end Hierarchy.DescentSixParty.GroupStage

end OAI
