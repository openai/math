import OAI.Hierarchy.ProbeFixedGlobalSource
import OAI.Hierarchy.ProbeAccountQuotes

namespace OAI
/-! # Payload and cooling votes obtained from the native, dated scalar scans -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "G" => v.privateArena P z width
local notation "layout" => JointHeader.scores P.joint z N k
variable (mem : Memory (wordBits z (2^v.W) copies)) (phase trial : ℕ)
local notation "u" => Attempt.outer phase trial
local notation "pg" => DeadlineROM.scorePage v.mesh layout z N k u
local notation "stock" => (f u).stockSource.old
local notation "s" => outerTime v.mesh v.finish phase
local notation "B" => repair C u
local notation "entry" => trialState C mem phase trial
local notation "source" => prepared C u entry
local notation "x" => (A).trial C mem phase trial
local notation "wall" => envelope v.W ((dyadicScale v.W)^8) s

private theorem digits_fit (precision : P.joint.precision=v.precision) :
    0<(pg).precision ∧ 8*GlobalTests.kinds N k≤(pg).precision := by
  change 0<P.joint.precision ∧ 8*(1+N*(2*k))≤P.joint.precision
  rw [precision,show Stages z (2^v.W)=publicStages v.W from fixed_stage_count z v.W]
  simpa only [Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using
    And.intro v.clock.precision_pos v.clock.lane_precision

private theorem output_floor : (G).base v.mesh (.attempt u)≤(B).tests.excess.out := by
  by_contra! bad
  exact (Nat.lt_irrefl _) ((v.event_prefix P z width r banks src tab dst owners (.attempt u) _ bad).1.2.2.1)

variable (precision : P.joint.precision=v.precision)
variable (R : GlobalTests.ReadStock
  (v.billedAccount P z width r banks src tab dst owners)
  ((v.billedAccount P z width r banks src tab dst owners).trial
    (v.nativeChart P z width r banks src tab dst owners) mem phase trial)
  (DeadlineROM.scorePage v.mesh (JointHeader.scores P.joint z (Stages z (2^v.W)) k)
      z (Stages z (2^v.W)) k (Attempt.outer phase trial))
  ((v.nativeFormats P z width (Attempt.outer phase trial)).stockSource.old)
  (GlobalTests.price (v.billedAccount P z width r banks src tab dst owners)
    (outerTime v.mesh v.finish phase) (probeBonus v.W) (routeCap (Stages z (2^v.W)) v.radius)
    (DeadlineROM.scorePage v.mesh (JointHeader.scores P.joint z (Stages z (2^v.W)) k)
      z (Stages z (2^v.W)) k (Attempt.outer phase trial)).precision)
  (prepared (v.nativeChart P z width r banks src tab dst owners) (Attempt.outer phase trial)
    (trialState (v.nativeChart P z width r banks src tab dst owners) mem phase trial)))

include precision R in
def cool_vote (date : phase≤v.mesh.inject+v.mesh.cool) :
    SumCalibration (B).tests.excess source
      (score (A).a (A).M (A).coefficient (maximizer (A).a (A).M s (A).coefficient (A).box ((A).bank.units (A).payloadWidth x)))
      ((wall+1/2)*(2^z:ℕ)) := by
  have digits:=v.digits_fit P z phase trial precision
  have heat : 0<(dyadicScale v.W)^8 := by unfold dyadicScale; positivity
  exact R.cool (B).tests.excess.out (fun _=>rfl) rfl
    (show 0≤(v.a:ℝ) by exact_mod_cast v.quadratic_pos.le)
    (by unfold probeBonus; positivity) ((v.W:ℝ)⁻¹^2) ((dyadicScale v.W)^8)
    ((show 0<(v.finish:ℝ) by exact_mod_cast v.clock.finish_pos).trans_le (v.real_times date).1)
    (sq_nonneg _) heat digits.1 digits.2

theorem cool_vote_threshold (date : phase≤v.mesh.inject+v.mesh.cool) :
    (v.cool_vote P z width r banks src tab dst owners mem phase trial precision R date).threshold=
      (2^z:ℕ)*(wall+3/8) := by
  change (wall+3/8)*(2^z:ℕ)=(2^z:ℕ)*(wall+3/8)
  ring

include precision R in
def payload_vote (injection : phase≤v.mesh.inject) :
    SumCalibration (B).tests.payload ((B).tests.excess.after source)
      (pairing (fun i=>((A).payload i:ℝ)) (maximizer (A).a (A).M 1 (A).coefficient (A).box ((A).bank.units (A).payloadWidth x)))
      ((3/2:ℝ)*(2^z:ℕ)) := by
  have digits:=v.digits_fit P z phase trial precision
  have lo:=v.output_floor P z width r banks src tab dst owners phase trial
  have second:=R.after_check (B).tests.excess ((v.global_page_floor P z width phase trial).trans lo)
    ((v.global_input_floor P z width phase trial).trans lo)
  rw [injection_time v.mesh _ injection] at second
  exact second.payload (B).tests.payload.out (fun _=>rfl) (fun i=>(v.acquisition_box z i).1)
    rfl rfl (show 0<(v.a:ℝ) by exact_mod_cast v.quadratic_pos) (by unfold probeBonus; positivity)
    (Nat.cast_nonneg _) digits.1 digits.2

theorem payload_vote_threshold (injection : phase≤v.mesh.inject) :
    (v.payload_vote P z width r banks src tab dst owners mem phase trial precision R injection).threshold=
      (2^z:ℕ)*(1+3/8:ℝ) := by
  change (1+3/8:ℝ)*(2^z:ℕ)=(2^z:ℕ)*(1+3/8:ℝ)
  ring

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
