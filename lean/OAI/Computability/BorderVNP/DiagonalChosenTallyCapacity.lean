import OAI.Computability.BorderVNP.DiagonalAssignedPowerBounds
import OAI.Computability.BorderVNP.DiagonalJointPacketOccurrences

/-! # All numerical inputs of the native residue reader on the selected schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Crossing PackedHistoryCircuit.Normalized Branch ResidueIndex ResidueBox
open _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical
open scoped Classical BigOperators

universe u

variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {extra E d Q A B j : ℕ}

/-- Exact field widths required by the residue reader at one calibrated
length. The data are uniform over every subsequent matrix and path choice. -/
def ReaderTallyInputsAt {K : Type*} [Field K] (cube : FixedCube K)
    {scales : EpochScales S (cube.pred+1) extra}
    (b : JointSchedule.{u} scales (E+1) d Q A B j) (n : ℕ) : Prop :=
    ∀ k : ℕ, n = k+1 →
      let r := stretch b.ρ n
      let size := stretch b.σ n
      let R := b.physical.teamsPred n+1
      let h := pairedTableParameters (k+1) size
      let ξ := (scales.τ:ℝ)/5
      let symbols := Cube.alphabet scales.α n
      ∀ W : ℝ, W ≤ (R*exterior ξ r n : ℕ) →
      let blocks := blocksFor W (cube.h*cube.b) (symbols^(cube.pred+1))
      ∀ (Gadget : Type) (deg : ℕ)
        (t : Tally (Fin R) (Fin h) Gadget (Nat.clog 2 (r*(2*k+1)+1)))
        (payload : ℕ), payload ≤ (r*n+1)^2 →
        (∀ g, (∑ team, t.counts team g) ≤ payload + Fintype.card (Packet cube.pred symbols blocks × Vertex (cube.pred+1))) →
        Fits (radius (batchDegree R h r k) deg) (parameterShift t.exponents) ∧
        (∀ i, t.exponents i < 2^b.physical.tally n) ∧
        (∀ g, (∑ team, t.counts team g) < 2^b.physical.multBits n) ∧
        (∀ g, (∑ team, t.counts team g) < 2^b.physical.tally n)

/-- All parameter powers and scalar multiplicities on one complete assigned row
fit the actual chart and machine fields. The threshold precedes the field chart,
history, payload, pin, and the matrix reader. The measured host and packet counts
refer to this row's own terminal layout. -/
theorem JointSchedule.eventually_reader_tally_inputs {K : Type*} [Field K] (cube : FixedCube K)
    {scales : EpochScales S (cube.pred+1) extra}
    (b : JointSchedule.{u} scales (E+1) d Q A B j) :
    ∀ᶠ n : ℕ in atTop, ReaderTallyInputsAt cube b n := by
  filter_upwards [b.eventually_lengths 0,b.eventually_word_capacity 288 7,
    b.eventually_payload_packet_capacity cube 1 2,eventually_ge_atTop 1] with n length words capacity hn
  intro k eqn
  subst n
  intro r size R h ξ symbols W occupied blocks Gadget deg t payload measured multiplicities
  have hr := stretch_one b.ρ (k+1)
  have nn : k+1 ≤ r*(k+1)+1 := (Nat.le_mul_of_pos_left _ hr).trans (Nat.le_succ _)
  have sizeLe : size ≤ r := by
    have bound := length.replication
    have power := Nat.le_self_pow (by decide : (24:ℕ) ≠ 0) (k+1+size+2)
    exact (show size ≤ k+1+size+2 by omega).trans (power.trans bound)
  have teams : R ≤ k+1 := by
    have exp : 2*(scales.α:ℝ) ≤ 1 := by linarith only [scales.alpha_small]
    have one : 1 ≤ ((k+1:ℕ):ℝ) := by exact_mod_cast hn
    have tight := length.teams.2.trans (Real.rpow_le_rpow_of_exponent_le one exp)
    rw [Real.rpow_one] at tight
    exact_mod_cast tight
  have hs : size ≤ r*(k+1)+1 := sizeLe.trans ((Nat.le_mul_of_pos_right _ hn).trans (Nat.le_succ _))
  have cap (g : Gadget) := capacity W occupied payload (∑ team, t.counts team g)
    (by simpa only [one_mul] using measured) (multiplicities g)
  exact ⟨t.assigned_shift deg,t.assigned_power_lt hr (teams.trans nn) hs words.2.2.2.1,
    fun g => (cap g).2.2.2,fun g => (cap g).2.2.1⟩

end Diagonal

end BorderVNP
end Computability
end OAI
