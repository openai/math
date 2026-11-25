import OAI.Hierarchy.DescentResetEstimatorWordRoom
import OAI.Hierarchy.DescentScheduledResetAtPorts
import OAI.Hierarchy.DescentPhysicalResetPrime

namespace OAI
/-! # Word bounds on the original scheduled reset arena -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ) (ports : Chronology.DatePorts)
    (floor w : ℕ)
local notation "m₀" => S.groupWidth k tail age+k
local notation "b₀" => S.localWalshBits p m₀ f (quota S.rounds)
local notation "a₀" => (scheduledAtPorts G S board k tail age p f g drift degree payload ordinary op s Z ports floor).inner
local notation "E₀" => (a₀).estimator ((a₀).stageStart (ports.priorStart k floor))

/-- The Walsh rows include the current registered degree and the entire source
actor axis. The public reset placement gives all three identities at its own base. -/
theorem scheduled_estimator_words
    (word : ResetEstimatorWords (S.hostSize age) m₀ b₀ (S.censusBits p) ports.venue.degree w) :
    3*(E₀).dim+((E₀).precision+Nat.clog 2 (E₀).hosts)+2≤w ∧
    Nat.clog 2 ((E₀).dim+2)+((E₀).dim+S.censusBits p)≤w ∧ S.hostSize age<2^w :=by
  let l:=laneBits m₀ payload b₀
  have small : l≤ m₀:=Nat.min_le_left ..
  have axes : (E₀).dim=m₀:=by
    change m₀-l+l=m₀
    exact Nat.sub_add_cancel small
  have rows : (E₀).hosts=S.hostSize age*(m₀+1+ports.venue.degree):=by
    change S.hostSize age*(m₀-l+l+1+ports.venue.degree)=_
    rw [Nat.sub_add_cancel small]
  have bits : (E₀).precision=b₀:=rfl
  rw [axes,rows,bits]
  exact ⟨word.score,word.header,word.host⟩

/-- Every positive payload holds the selected receiver pitch, including the
case in which the dictionary quotient is zero and the pitch is one. -/
theorem receiver_lanes_le (previous nextM C packet operands roles token : ℕ)
    (positive : 0<payload) :
    2^(receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      operands roles token ports.venue)≤payload :=by
  have lanes (m b : ℕ) : 2^(laneBits m payload b)≤payload:=by
    by_cases zero : payload/(8*b)=0
    · simpa [laneBits,zero,Nat.log_zero_right] using (show 1≤payload from positive)
    · calc
        2^(laneBits m payload b)≤2^(Nat.log 2 (payload/(8*b))):=
          Nat.pow_le_pow_right (by decide) (min_le_right ..)
        _ ≤ payload:= (Nat.pow_log_le_self 2 zero).trans (Nat.div_le_self ..)
  exact lanes _ _

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
