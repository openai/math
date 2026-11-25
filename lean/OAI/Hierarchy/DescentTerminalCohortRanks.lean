import OAI.Hierarchy.DescentTerminalCohortNumbering
import OAI.Hierarchy.DescentTerminalCohortFiber

namespace OAI
/-! # The true frozen-cohort rank is consecutive within every surviving venue -/

namespace Hierarchy.DescentTerminalCohortRanks
open Computability.BorderVNP.FragmentBucket Computability.BorderVNP.Crossing.Profile ProtocolRAMPortRanks
open scoped Classical BigOperators
noncomputable section

theorem earlier {I : Type} [Fintype I] {n : ℕ} (chart:I≃Fin n) (rank:I↪ℕ)
    (read:∀z,rank z=(chart z).val) (s:ℕ) (z:I) :
    «prefix» (fun _:I=>s) rank z=rank z*s := by
  unfold «prefix»
  rw [Finset.sum_filter,←chart.symm.sum_comp]
  simp only [read,Equiv.apply_symm_apply,←Finset.sum_filter]
  have same : Finset.univ.filter (fun i:Fin n=>i.val<(chart z).val)=Finset.Iio (chart z) := by ext;simp
  rw [same,Finset.sum_const,Fin.card_Iio,nsmul_eq_mul]
  simp

end
end Hierarchy.DescentTerminalCohortRanks

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height (initialGroup X S.copies (S.firstWidth G.b p))}
    {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0<p)

open DescentGL DescentColonies DescentExterior PinCohorts
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace NativeBranch
variable {tail : ℕ} (base : S.baseGroups=2^tail)
local notation "trace" => pinSpine X G S b hp base
local notation "E" => Fintype.card (Port P X.width)
local notation "H" => S.hostSize S.length
local notation "a" => S.groupWidth k tail S.length+k
local notation "N" => ((Epochs.finish G hu he r).state c).graph
local notation "A" => b.target.placement
local notation "f" => b.path.frozen
local notation "Cohort" => Fin (E*2^f)


open DescentTerminalCohortRanks
local notation "name_" => cohortHome X G S b hp base

def densePinEquiv (v:(N).Site) : Attached N v ≃ Fin (Computability.BorderVNP.FragmentBucket.count name_ (b.target.home v)) :=
  (attachedCohorts X G S b hp base v).trans (numbered name_ (b.target.home v))

theorem densePin_read (v:(N).Site) (z:Attached N v) :
    densePin X G S b hp base v z=(densePinEquiv X G S b hp base v z).val :=
  (numbered_read name_ _ ((attachedCohorts X G S b hp base v) z)).symm

theorem densePin_prefix (v:(N).Site) (pieces:ℕ) (z:Attached N v) :
    ProtocolRAMPortRanks.«prefix» (fun _:Attached N v=>pieces) (densePin X G S b hp base v) z=
      densePin X G S b hp base v z*pieces :=
  earlier _ _ (densePin_read X G S b hp base v) pieces z

end NativeBranch
end
end Hierarchy.DescentSixParty

end OAI
