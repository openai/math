import OAI.Hierarchy.DescentResetWalshScale
import OAI.Hierarchy.DescentGlobalControlRoom

namespace OAI
/-! # Common height for the signed-basis matrix and the depth, level, and load header -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentPackedWalsh Filter
noncomputable section

theorem matrix_and_total {F : Type} [Field F] (G : PoweredGadget F) (t f g reset B T : ℕ) :
    ∀ᶠ h : ℕ in atTop, ∀ copies tail i p,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset copies tail
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let m:=S.groupWidth k tail i+k
      p≤h → tail≤T*(Nat.log 2 h+1)^2 → i≤S.length →
        m*m≤h/2 ∧ Nat.clog 2 (m+2)+(m+S.censusBits p)≤h/2 := by
  let C:=localCoefficient G t f g reset (quota t) T
  filter_upwards [dyadic_log_room (2*C*C) 4, eventually_actual_width G t f g reset B (quota t) T]
    with h quartic word
  intro copies tail i p J S k m pay tailFit age
  let L:=Nat.log 2 h+1
  let b:=S.localWalshBits p m f (quota t)
  have original : b≤C*L^2 :=
    actual_width G t J f g reset copies tail i h p (quota t) T pay (Nat.div_le_self ..) tailFit age
  have dim : m≤b := by dsimp [b,AtomSchedule.localWalshBits,DescentWalshPrecision.bits];omega
  have mass : S.censusBits p≤b := by dsimp [b,AtomSchedule.localWalshBits,DescentWalshPrecision.bits];omega
  have sq:=Nat.mul_le_mul (dim.trans original) (dim.trans original)
  have upper : m*m*2≤h := calc
    _ ≤ (C*L^2)*(C*L^2)*2 := Nat.mul_le_mul_right 2 sq
    _ = (2*C*C)*L^4 := by ring
    _ ≤ h := quartic
  have actual : m+Nat.clog 2 (m+2)+8*b≤h/2 := (word copies tail i p pay tailFit age).2.2
  exact ⟨(Nat.le_div_iff_mul_le (by decide : 0<2)).2 upper,by omega⟩

/-- A matrix row and its group-chunk address share a half-word control key. -/
theorem original_coordinate_key {F : Type} [Field F] (G : PoweredGadget F) (t f g reset B T : ℕ) :
    ∀ᶠ h : ℕ in atTop, ∀ copies tail i p,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset copies tail
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let m:=S.groupWidth k tail i+k
      p≤h → tail≤T*(Nat.log 2 h+1)^2 → i≤S.length → (m+1)^2≤h/2 := by
  let C:=localCoefficient G t f g reset (quota t) T
  filter_upwards [dyadic_log_room (2*(C+1)^2) 4] with h quartic
  intro copies tail i p J S k m pay tailFit age
  let L:=Nat.log 2 h+1
  let b:=S.localWalshBits p m f (quota t)
  have original : b≤C*L^2 :=
    actual_width G t J f g reset copies tail i h p (quota t) T pay (Nat.div_le_self ..) tailFit age
  have dim : m≤b := by dsimp [b,AtomSchedule.localWalshBits,DescentWalshPrecision.bits];omega
  have positive : 1≤L^2 := Nat.succ_le_of_lt (Nat.pow_pos (Nat.succ_pos _))
  have bound : m+1≤(C+1)*L^2:=by nlinarith only [dim,original,positive]
  apply (Nat.le_div_iff_mul_le (by decide : 0<2)).2
  calc
    (m+1)^2*2 ≤ ((C+1)*L^2)^2*2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left bound 2)
    _ = (2*(C+1)^2)*L^4 := by ring
    _ ≤ h := quartic

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
