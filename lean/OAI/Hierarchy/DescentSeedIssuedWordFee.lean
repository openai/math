import OAI.Hierarchy.DescentSeedSelectedClock
import OAI.Hierarchy.DescentSeedOriginRateNumbers
import OAI.Hierarchy.DescentMeasuredResetLaneNumbers

namespace OAI
/-! # Charging the actual seed initializer at the same cutoffs as the native epoch -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentPackedWalsh DescentSeedRoot
open DescentDyadicSpan DescentColonies DescentInitialHost DescentPackedSeed Catalyst Filter
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

private theorem scale_up (J : ℕ) {a b : ℕ} (le : a ≤ b) : scale J a ≤ scale J b :=
  Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ le)

/-- The selected program uses both genuine pitches, with the separate seven
argument pages and the exact original seed validator. The native Granularity
theorem supplies the three socket inequalities in the conclusion. The lower
bounds on τ and B can be imposed on the same calibration as the other dates. -/
theorem issued_fee (t f g reset drift degreeMax quota e : ℕ) :
    ∃a b : ℕ,∀ τ B factor : ℕ,
      a+b+3+(e+5) ≤ τ → 0 < B → b+2 ≤ B →
      2*((2+hostRate t reset*(t+1)+(a+b)+1+1)+5+e) ≤ B →
      ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
        ∀ M q p degree w base field wire history header : ℕ,
        let S:=stageNumbers G t J f g reset M (tail τ J)
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        let l:=selectedLayout G S h k (tail τ J) g p drift degree f quota base field wire history
        0 < M → 0 < q → q ≤ scale J e → h ≤ 32*(q*p) → 0 < p → p ≤ h → S.firstWidth G.b p ≤ h → degree ≤ degreeMax → w+1 ≤ factor*h →
        ∀{c pins : ℕ} (X : Approximation F c pins) (publicWide : Fintype.card (Vertex X) ≤ span M)
          (digits : Fin S.copies≃Fin (S.groupCount 0)×Block k),
          (Input.wideTicks (S:=S) (k:=k) (H:=span M) X l h+
            7*DescentStaticWordColumn.names (Input.wideNode X digits publicWide l header h w))*
              (w+1)*2^J ≤ 2*(M*(S.copies*p)) :=by
  obtain ⟨donor,priced⟩:=first_donor_amount_rate G t f g reset
  let α:=Nat.clog 2 G.b*(t+1)
  let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let β:=donor+κ+3
  refine ⟨α,β,?_⟩
  intro τ B factor τfit pos widthCut Bfit
  let C:=50000000*(16*factor)
  have laneBound : 2*κ ≤ B :=by dsimp only [β] at widthCut Bfit;omega
  filter_upwards [calibration_at G t f g reset (α+β) (α+β) e C 0 τ (by omega) B pos (by omega),
    first_native_widths G t f g reset drift degreeMax quota τ B pos,
    measured_lane_room G t f g reset τ B quota laneBound,age_room B pos,eventually_ge_atTop 1]
      with h ledger widths room age hp
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro M q p degree w base field wire history header host qpos qbound packing pp pw ss de cpu c pins X publicWide digits
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let l:=selectedLayout G S h k (tail τ J) g p drift degree f quota base field wire history
  let d:=firstDonor G S g k p
  let wal:=firstPrecision S k (tail τ J) p f quota
  let r:=2^k
  let bit:=DescentOperandWidth.recordBits G S k (tail τ J) drift degree p
  let src:=S.firstWidth G.b p
  let price:=venuePrice G S factor g k (tail τ J) p f quota
  let cost:=(Input.wideTicks (S:=S) (k:=k) (H:=span M) X l h+
    7*DescentStaticWordColumn.names (Input.wideNode X digits publicWide l header h w))*(w+1)
  have dsmall : d ≤ scale J donor :=priced J M (tail τ J) p
  obtain ⟨wordBound,selectorBound,walshBound⟩:=widths M p degree src pw de ss
  have kk : r ≤ scale J κ := groupRateAt t J S.hostGain S.capGain (cutRate t f g)
  have ep:=epoch_room h B β hp widthCut age.1
  have enough (n : ℕ) (little : n ≤ scale J β) : 4*n ≤ h :=(Nat.mul_le_mul_left 4 little).trans ep
  have unitD : 0 < d :=by
    exact (Nat.succ_pos _).trans_le ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  have unitW : 0 < wal :=Nat.succ_pos _
  have dβ:=dsmall.trans (scale_up J (by dsimp only [β];omega : donor ≤ β))
  have bβ:=wordBound.trans (scale_up J (by dsimp only [β];omega : 3 ≤ β))
  have sβ:=selectorBound.trans (scale_up J (by dsimp only [β];omega : 2 ≤ β))
  have bill:=Input.selected_cpu G S h w factor k (tail τ J) g p drift degree f quota base field wire history header
    X digits publicWide host rfl rfl cpu unitD (by have:=enough d dβ;omega) unitW
    (room M 0 p (Nat.zero_le _) pw) (enough bit bβ) (by have:=enough _ sβ;exact (Nat.mul_le_mul_right _ (by decide : 2 ≤ 4)).trans this)
  have wr : wal*r ≤ scale J β :=((Nat.mul_le_mul walshBound kk).trans_eq (scale_mul J 3 κ)).trans
    (scale_up J (by dsimp only [β];omega))
  have signed : price ≤ 16*factor*scale J β :=by
    dsimp only [price,venuePrice]
    split
    · rw [Nat.mul_assoc (16*factor)]
      exact Nat.mul_le_mul_left _ wr
    · exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide : 4 ≤ 16)) dβ
  have operand : 8*factor*bit ≤ 16*factor*scale J β := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide : 8 ≤ 16)) bβ
  have selector : 4*factor*digitsNeeded src ≤ 16*factor*scale J β :=Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide : 4 ≤ 16)) sβ
  have arg : src/p ≤ scale J α :=(first_argument_count S G.b p pp).le.trans (grainRate G.b t J)
  obtain ⟨hi,lo⟩:=price_scales J α β factor (16*factor) (src/p) r price (8*factor*bit)
    (4*factor*digitsNeeded src) arg (kk.trans (scale_up J (by dsimp only [β];omega))) signed operand selector
  obtain ⟨at0,sum⟩:=zero_receipt S h _ _ cost bill
  have highC : 50000000*factor ≤ C:= by dsimp only [C];omega
  have charged:=ledger M q p _ _ qpos qbound packing
    (by simpa using hi.trans (Nat.mul_le_mul_left (scale J (α+β)) highC)) (by simpa [C] using lo) (atZero S cost) at0
  change (∑i : Fin (S.length+1),atZero S cost i)*2^J ≤ 2*(M*(S.copies*p)) at charged
  rw [sum] at charged
  exact charged

end
end Hierarchy.DescentDatedSeedStartup

end OAI
