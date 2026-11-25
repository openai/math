import OAI.Hierarchy.DescentCensusCalendarCapacity
import OAI.Hierarchy.DescentCensusPrecision
import OAI.Hierarchy.DescentPackedStageCensus
import OAI.Hierarchy.DescentOccurrenceAllowance

namespace OAI
/-! # One branch-independent local precision and packed-census invoice -/

namespace Hierarchy.DescentCompiler.AtomSchedule
open DescentSIMDLookup
theorem census_bits_pos (S : AtomSchedule) (p : ℕ) (hp : 0<p) : 0<S.censusBits p := by
  have step : 0<Nat.clog 2 (p+1) := by
    by_contra h
    have zero : Nat.clog 2 (p+1)=0 := by omega
    have bound:=Nat.le_pow_clog (b:=2) (by decide) (p+1)
    rw [zero,pow_zero] at bound
    omega
  unfold censusBits
  omega

theorem census_lane_max (S : AtomSchedule) (p k : ℕ) :
    max (S.censusLane p k) (S.censusBits p*2^k)=S.censusLane p k := by
  unfold censusLane
  exact max_eq_left (Nat.mul_le_mul_right _ (by omega))

theorem census_invoice (S : AtomSchedule) (first second : Banks) (H J k p w : ℕ)
    (room : 2*S.censusLane p k≤w) :
    DescentSixParty.PackedCensus.clocks first second H J (lanes w (S.censusLane p k))*w ≤
      8*w+88*(H*w+4*H*J*S.censusLane p k) := by
  have nonzero : 0<S.censusLane p k := Nat.mul_pos (by omega) (Nat.two_pow_pos _)
  simpa [S.census_lane_max] using DescentSixParty.PackedCensus.clock_invoice first second H J
    (S.censusLane p k) (S.censusBits p*2^k) w (by rwa [S.census_lane_max]) (by rwa [S.census_lane_max])

end Hierarchy.DescentCompiler.AtomSchedule

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler
open scoped Classical
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
  {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (S : AtomSchedule)
theorem census_caps {p : ℕ} (ready : A.StateBounds S i) (height : 0<S.height)
    (age : i≤S.length) (grain : A.z=S.grainAt G.b p i)
    (wire : A.wire=S.epochPower^S.priceExponent) (base : G.b≤2^S.capGain) :
    2*A.cap≤S.censusCapacity ∧ A.wire*(A.z*G.b)*A.cap<2^(S.censusBits p) :=
  A.census_caps_at S ready height age grain wire base

end Hierarchy.DescentSixParty.GroupStage

end OAI
