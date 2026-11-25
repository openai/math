import OAI.Hierarchy.ProbeFixedPhase
import OAI.Hierarchy.ProtocolRAMCalendarGlobalRoom
import OAI.Hierarchy.ProtocolRAMCalendarGlobalHeader
import OAI.Hierarchy.ProbeFixedGuardPages

namespace OAI
/-! # Accumulator and threshold space for both global scans before admission -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe CoreBoard PurchaseCT
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)

def maxVoteThreshold : ℝ := max 1 ((v.W:ℝ)⁻¹^2*(1/(dyadicScale v.W)^8))

def voteHeight :=
  let l : GlobalTests.Layout := ⟨0,0,0,v.precision⟩
  max (GlobalTests.kinds (publicStages v.W) k *
    GlobalTests.unitBound l (publicStages v.W) k (v.basePhase 0))
    ⌈(v.precision:ℝ)*(v.maxVoteThreshold+3/8)⌉₊

theorem vote_cutoff (t : ℝ) :
    (1:ℝ)≤v.maxVoteThreshold ∧ envelope v.W ((dyadicScale v.W)^8) t≤v.maxVoteThreshold :=
  ⟨le_max_left ..,(mul_le_mul_of_nonneg_left (min_le_right ..) (sq_nonneg _)).trans (le_max_right ..)⟩

variable (P : v.Placement) (z width : ℕ)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "l₀" => JointHeader.scores P.joint z N k
variable (a : Attempt)
local notation "pg" => DeadlineROM.scorePage v.mesh l₀ z N k a
local notation "s" => deadline v.mesh v.finish (v.basePhase width) a

theorem vote_accumulator_size (precision : P.joint.precision=v.precision) (height : v.voteHeight≤z) :
    GlobalTests.rows z N k*GlobalTests.unitBound pg N k s<2^W := by
  apply GlobalTests.large_room
  have hn : N=publicStages v.W := fixed_stage_count z v.W
  rw [hn]
  change GlobalTests.kinds (publicStages v.W) k *
    (∑i : Fin (GlobalTests.kinds (publicStages v.W) k),
      ⌊(P.joint.precision:ℝ)*GlobalTests.upper s i.val⌋₊)≤z
  rw [precision]
  exact (le_max_left ..).trans height

theorem vote_bound_size (precision : P.joint.precision=v.precision) (height : v.voteHeight≤z)
    {baseline : ℝ} (allowed : baseline≤v.maxVoteThreshold) :
    GlobalTests.bound pg z baseline<2^W := by
  let constant:=⌈(v.precision:ℝ)*(v.maxVoteThreshold+3/8)⌉₊
  have cutoff : baseline+3/8 ≤ v.maxVoteThreshold+3/8 := by linarith only [allowed]
  have coeff : (v.precision:ℝ)*(baseline+3/8)≤constant :=
    (mul_le_mul_of_nonneg_left cutoff (Nat.cast_nonneg v.precision)).trans
      (Nat.le_ceil ((v.precision:ℝ)*(v.maxVoteThreshold+3/8)))
  apply Nat.lt_of_le_of_lt _ (GlobalTests.linear_room z (2^v.W) constant ((le_max_right ..).trans height))
  unfold GlobalTests.bound
  change ⌈(P.joint.precision:ℝ)*scoreCut (2^z) baseline⌉₊≤_
  rw [precision,Nat.ceil_le]
  change (v.precision:ℝ)*((baseline+3/8)*(2^z:ℕ))≤((2^z*constant:ℕ):ℝ)
  rw [Nat.cast_mul,←mul_assoc,mul_comm ((v.precision:ℝ)*_)]
  exact mul_le_mul_of_nonneg_left coeff (Nat.cast_nonneg _)

/-- The caller supplies the resident scalar page and earlier stock at the entrance to
this individual pass. Its write region and all later calendar events play no role. -/
theorem vote_sum_size (precision : P.joint.precision=v.precision) (height : v.voteHeight≤z)
    (pay : Bool) (out cutoff : ℕ) (old : Bank) (m : Memory W)
    (loaded : GlobalTests.Resident pg z N k s m) (room : GlobalTests.rows z N k<2^W)
    (stride : (pg).stride≤2^z) (padded : GlobalTests.rows z N k≤old.size)
    (amounts : ∀i : Fin (GlobalTests.rows z N k),(m (old.base+i.val)).val<(pg).stride)
    (hot : 0<(s).time) :
    (∑i,(GlobalTests.check pg z N k pay out cutoff old).score m i)<2^W := by
  have size:=v.vote_accumulator_size P z width a precision height
  have rows : 0<GlobalTests.rows z N k := by
    rw [GlobalTests.rowCount]
    exact Nat.mul_pos (by unfold GlobalTests.kinds; omega) (Nat.two_pow_pos _)
  have step : GlobalTests.unitBound pg N k s<2^W :=
    (Nat.le_mul_of_pos_left _ rows).trans_lt size
  have widthRoom : GlobalTests.span pg N k<2^W :=
    (Nat.mul_le_mul_left (GlobalTests.kinds N k) stride).trans_lt room
  have aPositive : 0<(s).a := by
    change 0 < (v.a : ℝ)
    exact_mod_cast v.quadratic_pos
  have pos (i : ℕ) : 0≤ (s).cap i := by
    change 0≤ if i=0 then (publicStages v.W:ℝ) else v.radius+1
    split <;> positivity
  have signed (i : ℕ) : 0≤ (s).bonus i := by
    change 0≤ if i=0 then 0 else (v.W:ℝ)⁻¹^4/(publicStages v.W*(probeHeat v.W)^2)
    split <;> positivity
  let dict:=GlobalTests.words pg z N k s pay out cutoff old m loaded room (GlobalTests.mask_room z N k).1
    padded widthRoom (GlobalTests.mask_values pg z N k stride) amounts
    (fun i=>(GlobalTests.valueWord_le pg s pay (GlobalTests.kind i) _ aPositive (signed _) (Nat.cast_nonneg _) hot (pos _)).trans_lt step)
  exact (GlobalTests.global_sum dict (fun i=>(GlobalTests.kind i).isLt) aPositive (fun i _=>signed i)
    (Nat.cast_nonneg _) hot (fun i _=>pos i)).trans_lt size

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
