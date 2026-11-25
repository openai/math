import OAI.Hierarchy.DescentPackedVerdictText
import OAI.Hierarchy.DescentPackedEpochRebased
import OAI.Hierarchy.DescentNamedVerdictPrice
import OAI.Hierarchy.DescentWideOriginalCalendarBill

namespace OAI
/-! The verdict fold at its actual mutable destination, with the original packed selector lanes. -/
namespace Hierarchy.DescentPackedEpochShelves
open DescentSixParty DescentCompiler DescentCompiler.TerminalScale DescentTerminalEpochChart
open DescentTerminalEpochDecoder DescentPackedEpochFold DescentStaticWordColumn DescentWideSeedFlags
noncomputable section
variable {A : Type}

def foldInvoice (work lo C grain seed w : ℕ) (ss : List (Source A)) (count exterior : ℕ→ℕ) :=
  let stages := controlsAt work lo C grain ss count exterior
  let dest := finalAt work lo grain ss
  bill seed dest stages+7*names (fold w seed dest stages)+1

theorem fold_original_bill (S : AtomSchedule) (work lo C B h bw seed : ℕ) (ss : List (Source A))
    (count exterior : ℕ→ℕ) (large : 2≤h) (field : 2*unit C≤h/2)
    (positive : 0<S.initialSites) (dates : ss.length≤S.initialSites)
    (population : seatBill ss≤S.length*S.batch) :
    foldInvoice work lo C (grain (h/2) C) seed bw ss count exterior*(h+1) ≤
      1024*originalBill S C B h := by
  let r := grain (h/2) C
  let stages := controlsAt work lo C r ss count exterior
  let dest := finalAt work lo r ss
  let ticks := bill seed dest stages
  have half : h+1≤4*(h/2) := by omega
  have paid : ticks*(h/2) ≤ 64*(h/2)+578*ss.length*(h/2)+680*seatBill ss*unit C := by
    dsimp only [ticks,dest,stages,r]
    rw [bill_at]
    exact invoice lo C (h/2) seed ss count exterior field
  have op : foldInvoice work lo C r seed bw ss count exterior ≤ 16*ticks :=
    fold_charge_le bw seed dest stages
  let H := S.hostSize 0*(S.groupCount 0*S.radix)
  let D := scale S.height ((S.rounds+1)*(S.hostGain+S.capGain+1)+11)
  have units : seatBill ss*unit C≤(H*D)*unit C :=
    Nat.mul_le_mul_right _ (selector_seats S (i:=0) (Nat.zero_le _) population)
  have dateCost := Nat.mul_le_mul dates (Nat.div_le_self h 2)
  have baseCost : h/2≤S.initialSites*h := (Nat.div_le_self h 2).trans (Nat.le_mul_of_pos_left _ positive)
  have extra : 48*unit C*H*D ≤ (1920*B+48*unit C)*H*D :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_left ..))
  calc
    _ ≤ (16*ticks)*(4*(h/2)) := Nat.mul_le_mul op half
    _ = 64*(ticks*(h/2)) := by ring
    _ ≤ 64*(64*(h/2)+578*ss.length*(h/2)+680*seatBill ss*unit C) :=
      Nat.mul_le_mul_left _ paid
    _ ≤ _ := by
      change _ ≤ 1024*(328*S.initialSites*h+(1920*B+48*unit C)*H*D)
      nlinarith only [baseCost,dateCost,units,extra,Nat.zero_le (S.initialSites*h),Nat.zero_le (H*D*unit C)]

end
end Hierarchy.DescentPackedEpochShelves

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalEpochDecoder DescentPackedEpochShelves DescentPackedEpochFold DescentSeedRoot
open DescentWideSeedFlags Catalyst Computability.BorderVNP.Crossing Filter
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tailSize n stageH C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n stageH C f g cut tailSize)
variable (branch : G.b≤2^S.capGain) (positive : 0<p) (room : 10*(X.size+1)≤S.initialSites)
variable (shorten : reentryRate stageH C*(1-(2-G.rate)/4)^S.rounds≤1/2)
variable (h bw : ℕ) (fit : S.firstWidth G.b p<2^bw)
set_option quotPrecheck false
local notation "chart_" => normalizedPackedChart X G S ordinary reset branch positive room shorten bw fit

theorem wide_fold_tariff (work lo seed B : ℕ) (count exterior : ℕ→ℕ) (large : 2≤h)
    (width : 2*unit G.C≤h/2) (dates : S.length≤S.initialSites) :
    foldInvoice work lo G.C (grain (h/2) G.C) seed bw (chart_).layout count exterior*(h+1) ≤
      1024*originalBill S G.C B h := by
  let r := (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
  let o := inputOrder X G S ordinary reset branch positive room shorten
  have shape := epochs_layout G _ _ r o (seedChart X S.copies (S.firstWidth G.b p) bw fit)
  have levels : (chart_).layout.length=S.height*S.rounds := by
    simpa [normalizedPackedChart,packedChart,seedChart,r,o] using shape.1
  have pops : seatBill (chart_).layout=epochSeats G _ _ r := by
    simpa [normalizedPackedChart,packedChart,seedChart,seatBill,r,o] using shape.2
  have span : (chart_).layout.length≤S.length := by
    rw [levels]; unfold AtomSchedule.length; rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm S.rounds]; omega
  exact fold_original_bill S work lo G.C B h bw seed (chart_).layout count exterior large width
    (by omega) (span.trans dates) (pops.trans_le (seats X G S ordinary reset branch positive room shorten))


/-- The word and instruction charge for all original approximations at a fixed provider height. -/
def WideFoldTariffAt (G : PoweredGadget F) (t f g resetGain τ B e h : ℕ) : Prop :=
  let J:=Nat.log 2 h/(2*B)
  ∀ (M : ℕ) {cp nP : ℕ} (X : Approximation F cp nP) (q p E k cut n stageH C tailSize bw : ℕ),
    let S:=stageNumbers G t J f g resetGain M (tail τ J)
    let s:=S.firstWidth G.b p
    ∀ (ordinary : OrdinaryRates G S k cut)
      (reset : ResetRates G S k (atRound S.rounds) n stageH C f g cut tailSize)
      (branch : G.b≤2^S.capGain) (positive : 0<p) (room : 10*(X.size+1)≤S.initialSites)
      (shorten : reentryRate stageH C*(1-(2-G.rate)/4)^S.rounds≤1/2) (fit : s<2^bw),
      0<q → q ≤ scale J e → h≤32*(q*s) → S.length≤M →
      ∀ (work lo seed : ℕ) (count exterior : ℕ→ℕ),
      let ch:=normalizedPackedChart X G S ordinary reset branch positive room shorten bw fit
      foldInvoice work lo G.C (grain (h/2) G.C) seed bw ch.layout count exterior*
        (h+1)*2^J ≤ 2048*((S.copies*s)*(M+2^J*E))

/-- The actual rebased verdict is paid at date zero of the same calibrated calendar. -/
theorem all_wide_fold_tariff (t f g resetGain τ B e : ℕ)
    (tailFit : 0+0+3+(e+5)≤τ) (den : 0<B)
    (widthFit : 2*((2+hostRate t resetGain*(t+1)+((t+1)*(hostRate t resetGain+capRate G t g+1)+11)+
      (0+1)+1)+5+e)≤B) :
    ∀ᶠ h : ℕ in atTop, WideFoldTariffAt G t f g resetGain τ B e h := by
  filter_upwards [original_calendar_price G t f g resetGain G.C τ B e tailFit den widthFit,
    eventually_ge_atTop (4*unit G.C+2)] with h quote large
  dsimp only [WideFoldTariffAt]
  intro M cp nP X q p E k cut n stageH C tailSize bw ordinary reset branch positive room shorten fit
    qpos qsize packed dates work lo seed count exterior
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g resetGain M (tail τ J)
  let s:=S.firstWidth G.b p
  have raw:=wide_fold_tariff X G S ordinary reset branch positive room shorten h bw fit work lo seed B
    count exterior (by omega) (by omega) dates
  have paid:=quote M q s qpos qsize packed
  have total:= (Nat.mul_le_mul_right (2^J) raw).trans
    (show 1024*originalBill S G.C B h*2^J≤1024*(2*(M*(S.copies*s))) by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ paid)
  exact total.trans (by
    rw [Nat.mul_add]; nlinarith only [Nat.zero_le ((S.copies*s)*(2^J*E))])


/-- Specialization to one original approximation. -/
theorem cofinal_wide_fold_tariff (t f g resetGain τ B e : ℕ)
    (tailFit : 0+0+3+(e+5)≤τ) (den : 0<B)
    (widthFit : 2*((2+hostRate t resetGain*(t+1)+((t+1)*(hostRate t resetGain+capRate G t g+1)+11)+
      (0+1)+1)+5+e)≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M q p E k cut n stageH C tailSize bw : ℕ,
        let S:=stageNumbers G t J f g resetGain M (tail τ J)
        let s:=S.firstWidth G.b p
        ∀ (ordinary : OrdinaryRates G S k cut)
          (reset : ResetRates G S k (atRound S.rounds) n stageH C f g cut tailSize)
          (branch : G.b≤2^S.capGain) (positive : 0<p) (room : 10*(X.size+1)≤S.initialSites)
          (shorten : reentryRate stageH C*(1-(2-G.rate)/4)^S.rounds≤1/2) (fit : s<2^bw),
          0<q → q ≤ scale J e → h≤32*(q*s) → S.length≤M →
          ∀ (work lo seed : ℕ) (count exterior : ℕ→ℕ),
          let ch:=normalizedPackedChart X G S ordinary reset branch positive room shorten bw fit
          foldInvoice work lo G.C (grain (h/2) G.C) seed bw ch.layout count exterior*
            (h+1)*2^J ≤ 2048*((S.copies*s)*(M+2^J*E)) := by
  filter_upwards [all_wide_fold_tariff G t f g resetGain τ B e tailFit den widthFit] with h paid
  exact fun M => paid M X

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
