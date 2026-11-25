import OAI.Computability.BorderVNP.DiagonalChosenTallyCapacity
import OAI.Computability.BorderVNP.DiagonalSignedReceivedScale

/-! # Length bounds for every marked report on the chosen signed grid -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace Diagonal

open Filter Crossing Branch TeamScales PackedHistoryCircuit.Normalized
open scoped Classical

universe u

section
variable {F : Type*} [Field F] {D m : ℕ} [NeZero D] {G : PaidIdentity F D m}
    {S : SiteSchedule G} {a extra E d Q A B j : ℕ} {s : EpochScales S a extra}

/-- One cutoff fits all numbered grammar marks and all their binary places.
It depends only on the chosen schedule, before the chart, its reader or a route
has been selected. -/
theorem JointSchedule.eventually_gridMarkWidths (b : JointSchedule.{u} s (E+1) d Q A B j) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let w := b.physical.word n
      pairedTableParameters n (stretch b.σ n) ≤ 2^w ∧ 1 ≤ r ∧ logWidth r n ≤ w := by
  filter_upwards [b.eventually_lengths 0,b.eventually_word_capacity 288 7,eventually_ge_atTop 1] with n lengths words hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let r := stretch b.ρ (k+1)
  let size := stretch b.σ (k+1)
  let h := pairedTableParameters (k+1) size
  have hr : 1 ≤ r := stretch_one ..
  have sizeLe : size ≤ r := by
    have power := Nat.le_self_pow (by decide : (24:ℕ) ≠ 0) (k+1+size+2)
    exact (show size ≤ k+1+size+2 by omega).trans (power.trans lengths.replication)
  have degree := assigned_degree_polynomial 1 r k size hr (by omega)
    (sizeLe.trans ((Nat.le_mul_of_pos_right _ (Nat.succ_pos k)).trans (Nat.le_succ _)))
  have bits : 0 < 2^Nat.clog 2 (r*(2*k+1)+1)-1 := by
    have cap := Nat.le_pow_clog (by decide : 1 < 2) (r*(2*k+1)+1)
    have pos : 0 < r*(2*k+1) := Nat.mul_pos hr (Nat.succ_pos (2*k))
    omega
  have capped : h ≤ batchDegree 1 h r k := by
    simpa only [batchDegree,one_mul] using Nat.le_mul_of_pos_right h bits
  exact ⟨(capped.trans (degree.trans_lt words.2.2.1).le),hr,words.1⟩

end

open Cover Epoch Packing Packing.DeckGrid Packing.Inherited
open PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {G : PaidIdentity F D m}
    {S : SiteSchedule G} {extra E d Q A B j : ℕ}
    (cube : FixedCube K) {scales : EpochScales S (cube.pred+1) extra}
    (b : JointSchedule.{0} scales (E+1) d Q A B j) (header n : ℕ)

/-- Space and digit widths of the actual receipt directory on the selected
batch, with its original deck depth, copies and chronological compiler mass. -/
abbrev GridReportScaleAt : Prop :=
  let r := stretch b.ρ n
  let depth := CoverScale.initialDepth (Epoch.Cube D) r n-1
  let axes := Fintype.card (Epoch.Cube D)
  let capacity := seedBoxCapacity n r axes depth (Fintype.card (Direction axes))
  let copies := TeamScales.width n scales.α
  let mass := S.publicProgramFactor^epochs scales.τ n*initialMass (D:=D) n r depth copies header
  let coefficient := (birthWordCoefficient G+8)*(BankCharges.bound G+1)*(S.populationFactor+2)
  let gadgets := Fintype.card (G.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)
  SignedReceivedScale (TeamScales.width n (1/5)) (TeamScales.width n (1/4)) (b.physical.word n) gadgets mass
    (max (tableLimit G) (max 8 capacity)) (signedMarkedLimit copies capacity coefficient mass)
    ((logWidth r n+1)^(E+2))

/-- On the same scheduled lengths, the enlarged phase degree bounds the true
received reports before any reader, table, route or assignment is chosen. -/
theorem JointSchedule.eventually_gridReportScale :
    ∀ᶠ n : ℕ in atTop, E+2 ≤ d → GridReportScaleAt cube b header n := by
  by_cases h : E+2 ≤ d
  · filter_upwards [b.eventually_signed_received_scale header
      (Fintype.card (G.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)) h] with n fits
    exact fun _ => fits
  · exact Filter.Eventually.of_forall (fun _ good => (h good).elim)

end Diagonal

end BorderVNP
end Computability
end OAI
