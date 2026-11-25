import OAI.Hierarchy.DescentNamedCohortFiber
import OAI.Hierarchy.DescentTerminalCohortRanks

namespace OAI
/-! # Exact per-vertex row ranks on the named physical epoch -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S radix R r c) (hp : 0<p)

open DescentGL DescentColonies DescentExterior PinCohorts
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace Branch
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

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
