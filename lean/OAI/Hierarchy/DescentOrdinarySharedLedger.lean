import OAI.Hierarchy.DescentOrdinaryOverlapReserve
import OAI.Hierarchy.DescentStageLedger

namespace OAI
/-! # Accounting for all ordinary-date rectangles and their shared static tables -/
namespace Hierarchy.DescentCompiler.TerminalScale
open Filter DescentSixParty DescentSIMDLookup
open scoped BigOperators

/-- Shared constants may grow with the fixed public setup. They do not draw on the
number of old or new per-site operand rows. -/
theorem shared_date (C K d saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀J M H G high low cost u : ℕ,J≤Nat.log 2 h→u≤K*(J+1)^d→2^h≤M→
      cost≤H*h*high+H*G*low+(C*2^u)*(2*(h+1)^2*2^(h/2))*h→
        cost≤H*h*high+H*G*low+M/(2^J)^saving := by
  filter_upwards [Overlap.charged_half_pages C K d saving] with h buy
  intro J M H G high low cost u age exponent ambient receipt
  exact receipt.trans (Nat.add_le_add_left (buy J u M age exponent ambient) _)

/-- Counts both fixed data rates at the full bus width, absorbing exactly the one
residual per emitted date into the nonempty original-site shared term. -/
theorem schedule_receipt {F : Type} [Field F] (G : PoweredGadget F) (t f g reset J M tail : ℕ)
    (h high low saving : ℕ) (positive : 0<h) :
    let S:=stageNumbers G t J f g reset M tail
    ∀i fee : ℕ, fee≤S.hostSize i*h*high+S.hostSize i*(S.groupCount i*S.radix)*low+M/(2^J)^saving →
      fee≤S.hostSize i*h*(high+1)+S.hostSize i*(S.groupCount i*S.radix)*low := by
  intro S i fee paid
  have radix : 0<S.radix:=Nat.two_pow_pos _
  have startSize : S.hostSize 0=M:=by change M*_ ^ (0:ℕ)=M;simp
  have source : M≤S.hostSize i:=startSize ▸ host_mono S (Nat.zero_le i) radix
  have bus : S.hostSize i≤S.hostSize i*h := Nat.le_mul_of_pos_right _ positive
  have shared : M/(2^J)^saving≤S.hostSize i*h := (Nat.div_le_self ..).trans (source.trans bus)
  rw [Nat.mul_add,Nat.mul_one]
  omega

/-- A receipt with a single half-word residue feeds the same actual finite calendar
and the same calibration as the prior ordinary and reset geometry. -/
theorem stage_ledger_shared {F : Type} [Field F] (G : PoweredGadget F) (t J f g reset M τ h p high low saving : ℕ)
    (S : AtomSchedule) (config : S=stageNumbers G t J f g reset M (tail τ J)) (positive : 0<h)
    (hostBought : ((S.length+1)*(high+1))*h≤p*2^(tail τ J))
    (itemBought : (S.length+1)*(2^S.hostGain)^S.length*low*2^J≤p)
    (fee : Fin (S.length+1)→ℕ)
    (paid : ∀i,fee i≤S.hostSize i.val*h*high+S.hostSize i.val*(S.groupCount i.val*S.radix)*low+M/(2^J)^saving) :
    (∑i,fee i)*2^J≤2*(M*(S.copies*p)) := by
  apply stage_ledger G t J f g reset M τ h p (high+1) low S config hostBought itemBought
  intro i
  subst S
  exact schedule_receipt G t f g reset J M (tail τ J) h high low saving positive i.val (fee i) (paid i)

end Hierarchy.DescentCompiler.TerminalScale

end OAI
