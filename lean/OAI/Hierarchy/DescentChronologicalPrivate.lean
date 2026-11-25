import OAI.Hierarchy.DescentNormalizedBundle
import OAI.Hierarchy.DescentChronologicalFee

namespace OAI
/-! # The true private cable width of the issued terminal archive -/

namespace Hierarchy.DescentSixParty.NativeBranch
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice DescentHistoryOrder
open Catalyst Computability.BorderVNP.Crossing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "q" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "ε" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => q*(wire:ℝ)
local notation "heightLimit" => GroupStage.depthBound (atRound S.rounds) n f g
local notation "start" => initialGroup X S.copies s
include X G S n h C f g p in
theorem archive_private {he : 0≤ε} {hu : 0≤u} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=heightLimit) (t:=S.rounds) S.height start}
    {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0<p) : privateMass (NativeBranch.archive X G S b hp).bit=b.path.privateCharge := by
  unfold NativeBranch.archive
  rw [Chronology.Path.archive_mass]
  change privateMass (DescentKernelHistory.BitDescription.initial X S.copies s (Chronology.epochsSource G r c))+
    b.path.privateCharge=b.path.privateCharge
  rw [initial_mass,Nat.zero_add]

include X G S n h C f g p in
theorem site_le {he : 0≤ε} {hu : 0≤u} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=heightLimit) (t:=S.rounds) S.height start}
    {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0<p) (v : ((Epochs.finish G hu he r).state c).graph.Site) :
    sitePrivate (NativeBranch.archive X G S b hp).bit v≤b.path.widthCharge :=
  (sitePrivate_le _ v).trans ((archive_private X G S b hp).le.trans b.path.privateCharge_le)

end
end Hierarchy.DescentSixParty.NativeBranch

namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentSixParty DescentCompiler DescentInitialHost DescentMixedRouter
open DescentResetInvoice DescentHistoryOrder Catalyst Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b≤2^S.capGain) (positive : 0<p) (room : 10*(X.size+1)≤S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds≤1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten

local notation "rowsAt" => normalizedIssuedRows X G S ordinary reset branch positive room shorten

/-- The normalized terminal stream's actual local hidden payload labels are paid by its own recorded path. -/
theorem normalized_private_grains (c : (Epochs.finish G _ _ (cert).choose).Choice) (v : ((Epochs.finish G _ _ (cert).choose).state c).graph.Site) :
    privateGrains p ((NativeBranch.archive X G S (rowsAt c) positive).bit.recipe v)≤(rowsAt c).path.widthCharge/p := by
  apply (Nat.le_div_iff_mul_le positive).mpr
  rw [((normalizedIssuedShape X G S ordinary reset branch positive room shorten c).sites v).privateGrains_mul]
  exact NativeBranch.site_le X G S (rowsAt c) positive v

end
end Hierarchy.DescentBundleHistory

end OAI
