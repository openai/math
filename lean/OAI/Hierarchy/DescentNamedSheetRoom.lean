import OAI.Hierarchy.DescentNamedResetSheetScale
import OAI.Hierarchy.DescentDatedCandidateSheetRate
import OAI.Hierarchy.DescentResetReceiverPitch
import OAI.Hierarchy.DescentDatedSmallAddress

namespace OAI
/-! # Address room for all candidate sheets in the scheduled reset -/
namespace Hierarchy.DescentDatedAddressBook.CandidateSheets
open Filter DescentResetCandidateDate DescentResetMixedWordRAM
noncomputable section
variable {ι : ℕ→Type*} {J : ℕ→ℕ}
variable (p : ∀h,ι h→ResetOutput)
set_option quotPrecheck false in
local notation "v" => fun h i=>(p h i).sheets

/-- Every table measured here occurs in the physical receiver's common lane
calibration. The two old block counts are the public residual window. -/
theorem room_from_schedule {shape original : ∀h,ι h→ℕ}
    (local_ : LocalFields J v shape original) (height : ∀ᶠ h:ℕ in atTop,J h≤h)
    (hosts : Bounded fun h i=>(v h i).hosts) (groups : Bounded fun h i=>(v h i).groups)
    (lanes : Bounded fun h i=>(p h i).receiver.lanes)
    (pitch : ∀h i,(v h i).lanes=(p h i).receiver.lanes)
    (positive : ∀h i,0<(v h i).lanes)
    (fine : ∀h i,2^(v h i).stemFine=(v h i).blocks) (residual : ∀h i,2^(v h i).stemResidual=(v h i).blocks)
    (matrix : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(v h i).stemDimension*(v h i).stemDimension≤C*h)
    (sparse : Bounded fun h i=>(v h i).sparseHosts) (donors : Bounded fun h i=>(v h i).donorSlots)
    (paid : ∀ᶠ h:ℕ in atTop,∀i b,b∈(p h i).rootUnits ∨ b∈(p h i).receiverUnits → b*(p h i).receiver.lanes≤h/2) :
    ScalarRoom v:=by
  obtain ⟨K,square⟩:=matrix
  have blocks:=local_.block.bounded height
  have inputs : DescentResetOriginalDonors.Layout.ScalarRoom (fun h i=>(v h i).originalDonors):=by
    refine ⟨sparse,groups,blocks,lanes.of_le (fun h i=>(pitch h i).le),donors,⟨1,?_⟩,⟨1,?_⟩⟩
    · filter_upwards [paid] with h fit
      intro i
      let s:=v h i
      have ok:=fit i (max s.stemSources.width s.metaBits) (.inr (by simp [ResetOutput.receiverUnits,s]))
      have smaller : s.stemSignedBits≤ s.stemSources.width:=Nat.le_max_left ..
      rw [←pitch h i] at ok
      exact (Nat.mul_le_mul_right _ (max_le_max_right s.metaBits smaller)).trans
        (ok.trans (by simpa only [Nat.one_mul] using Nat.div_le_self h 2))
    · filter_upwards [paid] with h fit
      intro i
      let s:=v h i
      have ok:=fit i (max s.selectorBits s.shortBits*(s.blocks+1)) (.inr (by simp [ResetOutput.receiverUnits,s]))
      rw [←pitch h i] at ok
      exact ok.trans (by simpa only [Nat.one_mul] using Nat.div_le_self h 2)
  have haloDigits : Bounded (fun h i=>2^(v h i).metaBits):=by
    apply Bounded.pow_of_linear (K:=1)
    filter_upwards [paid] with h fit
    intro i
    have ok:=fit i (v h i).metaBits (.inl (by simp [ResetOutput.rootUnits]))
    rw [←pitch h i] at ok
    exact (Nat.le_mul_of_pos_right _ (positive h i)).trans
      (ok.trans (by simpa only [Nat.one_mul] using Nat.div_le_self h 2))
  refine ⟨blocks,hosts,groups,lanes.of_le (fun h i=>(pitch h i).le),local_.slots.bounded height,
    local_.jobs.bounded height,local_.contact.bounded height,local_.private_.bounded height,inputs,haloDigits,?_,
    Bounded.pow_of_linear square,blocks.of_le (fun h i=>(fine h i).le),blocks.of_le (fun h i=>(residual h i).le),?_⟩
  · refine ⟨1,?_⟩
    filter_upwards [paid] with h hh
    intro i
    have ok:=hh i (v h i).stemSources.width (.inr (by simp [ResetOutput.receiverUnits]))
    rw [←pitch h i] at ok
    simpa only [Nat.one_mul] using ok.trans (Nat.div_le_self h 2)
  · refine ⟨1,?_⟩
    filter_upwards [paid] with h hh
    intro i
    let s:=v h i
    have words (b : ℕ) (member : b∈(p h i).receiverUnits) : b*s.lanes≤h:=by
      have raw:=hh i b (Or.inr member)
      change b*(v h i).lanes≤h
      rw [pitch]
      exact raw.trans (Nat.div_le_self ..)
    have «meta»:=words (s.metaBits*10) (by simp [s,ResetOutput.receiverUnits])
    have twice:=words (s.shortBits+s.shortBits) (by simp [s,ResetOutput.receiverUnits])
    have joined:=words (s.selectorBits+s.shortBits) (by simp [s,ResetOutput.receiverUnits])
    have code:=words s.argBits (by simp [s,ResetOutput.receiverUnits])
    have lead:= (Nat.le_mul_of_pos_right s.argBits (positive h i)).trans code
    change _≤1*h ∧ _≤1*h ∧ _≤1*h ∧ _≤1*h ∧ _≤1*h ∧ _≤1*h
    rw [Nat.one_mul]
    refine ⟨?_,?_,words _ (by simp [ResetOutput.receiverUnits]),
      words _ (by simp [ResetOutput.receiverUnits]),lead,words _ (by simp [ResetOutput.receiverUnits])⟩
    · change (s.metaBits*9+s.metaBits)*s.lanes≤h
      rw [show s.metaBits*9+s.metaBits=s.metaBits*10 by omega]
      exact «meta»
    · exact max_le joined twice

end
end Hierarchy.DescentDatedAddressBook.CandidateSheets

end OAI
