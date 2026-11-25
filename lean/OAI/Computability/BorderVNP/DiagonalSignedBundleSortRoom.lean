import OAI.Computability.BorderVNP.DiagonalSignedOriginalBankCapacity
import OAI.Computability.BorderVNP.DiagonalFrozenSignedOperandRoom
import OAI.Computability.BorderVNP.PackedFrozenBundleShape
import OAI.Computability.BorderVNP.CellPacketGeometryRate

/-! # Dimensions of the actual six-word bundle sort and description prefix scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Cover Epoch TeamScales Packing DeckGrid Inherited Filter ExternalSew
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube
set_option maxHeartbeats 2400000
set_option maxRecDepth 6000

private theorem padded_scans {J desc h cells : ℕ} (hh : 64≤h) (volume : J*desc ≤ 3*h^2+1)
    (positive : 1≤desc) (short : desc ≤ h) (small : cells ≤ h) :
    2^Nat.clog 2 J*desc < h^3 ∧ 2^Nat.clog 2 (cells+6*J+cells) ≤ h^3 := by
  have size : J ≤ J*desc := Nat.le_mul_of_pos_right _ positive
  have sq : h ≤ h^2 := (Nat.le_mul_of_pos_left h (by omega)).trans_eq (pow_two _).symm
  have cube : 64*h^2 ≤ h^3 := (Nat.mul_le_mul_right _ hh).trans_eq (by ring)
  have cost := Nat.mul_le_mul_right desc (CellPacketGeometry.LiveWords.pow_clog_le J)
  rw [show 2*(J+1)*desc=2*(J*desc)+2*desc by ring] at cost
  have pad := CellPacketGeometry.LiveWords.pow_clog_le (cells+6*J+cells)
  omega

private theorem birth_le_field {siteMass storage birth other room : ℕ}
    (h : max (15*siteMass) storage + max (max birth other) (max 1 (15*siteMass))+1 < room) :
    birth < room := by omega

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

/-- Header constituent widths, original-description scan, and the padded
sort of six fields plus two markers for every real cell all fit the very
same native word as the signed packet. -/
theorem JointSchedule.eventually_signed_bundle_sort_room (b : JointSchedule s E deg Q A B j) (header : ℕ) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let T := epochs s.τ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      let axes := Fintype.card (Cube D)
      let J := (epochCopies S)^T*GridHosts.tileCount axes d
      let copies := width n s.α
      let cap := seedBoxCapacity n r axes d (Fintype.card (Direction axes))
      let desc := seedDescriptionWidth n r axes d (header*logWidth r n) (BottomGridBank.bodyBudget cap)
      ∀ w ≥ 60*logWidth r n, ∀ cells ≤ r*n,
        copies < 2^w ∧ cap < 2^w ∧ desc < 2^w ∧ 2^Nat.clog 2 J*desc < 2^w ∧
          cells < 2^(60*logWidth r n) ∧ 2^Nat.clog 2 (cells+6*J+cells) ≤ 2^w := by
  filter_upwards [b.eventually_signed_original_bank header,b.eventually_signed_description_fit header,
    b.eventually_frozen_operand_room header (fun _ => 0),eventually_ge_atTop 64] with n charges length operands hn
  intro r T d axes J copies cap desc w hw cells hc
  let H := logWidth r n
  let h := 2^H
  have hr := stretch_one b.ρ n
  have rn : r*n ≤ h := by
    have pos : 2*r*n ≤ 2^H := by
      rw [show 2*r*n = 2*n*r by ring]
      dsimp only [H]
      rw [Shortening.PublicCapacity.public_logWidth]
      exact Nat.le_pow_clog (by decide) _
    have le : r*n ≤ 2*r*n := by nlinarith only
    exact le.trans pos
  have nh : n≤h := (Nat.le_mul_of_pos_left _ hr).trans rn
  have digits := operands w hw
  have low : max 2 (max copies cap) < 2^w := birth_le_field digits.1
  have charged := charges (fun _ : Fin J => (0 : Fin 1)) 0 0 0 (Nat.zero_le _) (Nat.zero_le _)
  change 0+0+(∑ _ : Fin J, if (0 : Fin 1)=0 then desc else 0) ≤ 3*(r*n)^2+1 at charged
  have raw : J*desc ≤ 3*(r*n)^2+1 := by
    simpa only [ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.zero_add] using charged
  have bigger : 3*(r*n)^2+1 ≤ 3*h^2+1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left rn 2)) 1
  have lib : 0 < BottomGridBank.bodyBudget cap := by
    unfold BottomGridBank.bodyBudget
    exact Nat.mul_pos (by omega) (by omega)
  have positive : 0<desc := lib.trans_le ((Nat.le_add_left _ _).trans (Nat.le_add_right _ _))
  have fits := padded_scans (hn.trans nh) (raw.trans bigger) positive (length.trans nh) (hc.trans rn)
  have Hpos : 1≤H := (GeometryAdviceRate.indexWidths hr (by omega : 1≤n)).1
  have power : h^3 ≤ 2^(60*H) := (pow_mul 2 H 3).symm.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have farther : 2^(60*H) ≤ 2^w := Nat.pow_le_pow_right (by decide) hw
  have up : h < 2^(60*H) := Nat.pow_lt_pow_right (by decide : 1<2) (by omega)
  exact ⟨by omega,by omega,(length.trans nh).trans_lt (up.trans_le farther),
    fits.1.trans_le (power.trans farther),(hc.trans rn).trans_lt up,fits.2.trans (power.trans farther)⟩

end Diagonal

end BorderVNP
end Computability
end OAI
