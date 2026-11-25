import OAI.Hierarchy.DescentNamedNormalizedChart
import OAI.Hierarchy.DescentTerminalEpochLayoutBill
import OAI.Hierarchy.DescentOrdinaryCountDates

namespace OAI
/-! # Ordinary verdict dates and the source rows of the normalized epoch chart -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentColonies DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentGL DescentCompiler DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)

private theorem ordinary_period_count (rounds pos : ℕ) :
    (Chronology.countDates pos (Chronology.kindPeriod rounds)).length=rounds := by
  induction rounds generalizing pos with
  | zero => rfl
  | succ rounds ih =>
    change (Chronology.countDates pos
      ((List.replicate (rounds+1) false) ++ [true])).length=rounds+1
    rw [List.replicate_succ]
    change (pos :: Chronology.countDates (pos+1) (Chronology.kindPeriod rounds)).length=rounds+1
    rw [List.length_cons,ih]

private theorem ordinary_calendar_count (rounds height pos : ℕ) :
    (Chronology.countDates pos (Chronology.kindCalendar rounds height)).length=height*rounds := by
  induction height generalizing pos with
  | zero => simp [Chronology.kindCalendar,Chronology.countDates]
  | succ height ih =>
    change (Chronology.countDates pos
      (List.replicate (height+1) (Chronology.kindPeriod rounds)).flatten).length=(height+1)*rounds
    rw [List.replicate_succ,List.flatten_cons,Chronology.countDates_append,List.length_append,
      ordinary_period_count]
    change rounds+(Chronology.countDates _ (Chronology.kindCalendar rounds height)).length=_
    rw [ih,Nat.succ_mul,Nat.add_comm]

include ordinary room in
/-- The original numbered host has a row available for every date up to its age. -/
theorem ordinary_age_room (i : ℕ) : i≤S.hostSize i := by
  have bits : 0<k:=by
    rw [ordinary.adr]
    unfold groupBits
    omega
  have radix : 2≤S.radix:=by
    rw [ordinary.radix]
    exact Nat.one_lt_two_pow bits.ne'
  have grow : 2≤2^S.hostGain*S.radix:=radix.trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  have initial : 0<S.initialSites:=by omega
  exact (Nat.lt_two_pow_self.le : i≤2^i).trans
    ((Nat.pow_le_pow_left grow i).trans (Nat.le_mul_of_pos_left _ initial))

/-- The native calendar skips exactly the reset dates. Its copy of ordinary verdicts
has one word for each source in the original epoch chart. -/
theorem scheduled_capture_length :
    (Chronology.countDates 0 (Chronology.kindCalendar S.rounds S.height)).length =
      (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).layout.length := by
  rw [ordinary_calendar_count]
  let run := (SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
  let order := inputOrder X G S ordinary reset branch positive room shorten
  let seedWidth := S.firstWidth G.b p
  have layout := (epochs_layout G _ _
    (H:=initial X S.copies seedWidth (S.groupCount 0) k (S.initialDigits ordinary.radix))
    run order (seedChart X S.copies seedWidth w fit)).1
  change _ = 0 + (S.height*S.rounds) at layout
  exact (Nat.zero_add _).symm.trans layout.symm

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
