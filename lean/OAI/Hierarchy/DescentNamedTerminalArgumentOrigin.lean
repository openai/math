import OAI.Hierarchy.DescentTerminalReachedPointerOrigin
import OAI.Hierarchy.DescentNamedTerminalPointerPins
import OAI.Hierarchy.DescentNamedHistoryShape
import OAI.Hierarchy.DescentNamedPrivateArchive

namespace OAI
/-! # Interpreting the terminal pointer at its attained home and archive address -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.archive Branch.bundleShape Branch.localNodes Branch.pinSpine Branch.originalPin
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)


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
local notation "freezeDepth_" => b.path.frozen
local notation "Cohort" => Fin (E*2^freezeDepth_)



local notation "homes" => cohortHome X G S b hp base
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "old" => b.origin.source
local notation "frozen" => (fun t:Cohort=>(finProdFinEquiv.symm t : Fin E×Fin (2^freezeDepth_)).2)
local notation "codeAt" => DescentTerminalFrozenRoster.book homes frozen

open DescentBundleHistory DescentLocalArchiveOrder DescentLocalPrivateNames DescentTerminalChronologicalBooks
open DescentTerminalPointerIssue DescentTerminalPointerDigits DescentStageEdgeReceipt
private def recipeBirth {F P : Type} [Field F] {D p R : ℕ} {bits : P → ℕ}
    {W : MarkedWorld F D P bits} (B : BitDescription W) (number : Local B)
    (shape : WorldShape p R B) (hp : 0 < p) (v : W.graph.Site) :
    ((shape.sites v).recipe hp).Node ↪ ℕ :=
  (number v).toEmbedding.trans Fin.valEmbedding

variable (stride : 1≤R)
private def argumentArchive : Chronology.Archive ((Epochs.finish G hu he r).state c) :=
  Branch.archive X G S (r:=r) (c:=c) b hp
local notation "arch_" => argumentArchive X G S b hp
private def argumentShape : WorldShape p R (arch_).bit :=
  Branch.bundleShape X G S (r:=r) (c:=c) b hp stride
local notation "schema_" => argumentShape X G S b hp stride
private def argumentNumbers : Local (arch_).bit :=
  Branch.localNodes X G S (r:=r) (c:=c) b hp
local notation "number_" => argumentNumbers X G S b hp
attribute [local irreducible] argumentArchive argumentShape argumentNumbers

variable (v : ((Epochs.finish G hu he r).state c).graph.Site) {nodes args oldNodes oldArgs : ℕ}
local notation "recipe_" => ((schema_).sites v).recipe hp
local notation "birth_" => recipeBirth (arch_).bit number_ schema_ hp v
local notation "order_" => b.target.order.trans Fin.valEmbedding
local notation "names_" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (groupRank (Fin.valEmbedding (n:=S.groupCount S.length)) (b.target.vertex.trans Fin.valEmbedding))
local notation "ports_" => (densePinEquiv X G S b hp base v).toEmbedding.trans Fin.valEmbedding
variable (nn : Fintype.card (((argumentShape X G S b hp stride).sites v).recipe hp).Node≤nodes) (aa : ∀u,(((argumentShape X G S b hp stride).sites v).recipe hp).arity u≤args)
    (on_ : Fintype.card (((argumentShape X G S b hp stride).sites v).recipe hp).Node≤oldNodes) (oa_ : ∀u,(((argumentShape X G S b hp stride).sites v).recipe hp).arity u≤oldArgs)
local notation "pos_" => slot recipe_ birth_ nn aa
local notation "old_" => slot recipe_ birth_ on_ oa_
local notation "netRank" => DescentTerminalPortChart.rank A order_ S b.target.valid names_ v ports_
local notation "rawPtr" => Reached.argumentPointer b.target (arch_).bit number_ schema_ hp (fun z=>z.1.val) oldArgs

/-- Four registered header digits name the original block.  At the terminal
host, the saved matrix and frozen roster convert its public copy into the
dense port ordinal used by the common terminal chip. -/
theorem terminal_argument_origin (t : CellInputs (A).degree (A).cap nodes args) (matrix roster : ℕ)
    (matrixAt : matrix=(matrixCode (trace).matrix).val)
    (rosterAt : roster=(codeAt (b.target.home v)).val)
    (pop : t.n=Fintype.card (recipe_).Node)
    (widths : ∀u:(recipe_).Node,t.arity (row recipe_ birth_ nn u)=(recipe_).arity u)
    (physical : ∀s:Slot recipe_,t.pointer (pos_ s)=rawPtr ⟨v,s.1⟩ s.2.val) :
    DescentTerminalPointerIssue.Origin (N) v recipe_ birth_ nn aa old_ netRank ports_
      (reindexed t (terminalPin initialBits a freezeDepth_ matrix roster)) :=by
  apply Reached.argument_origin b.target (arch_).bit number_ schema_ hp (fun z=>z.1.val)
    v nn aa on_ oa_ (densePinEquiv X G S b hp base v) _ t pop widths physical
  intro z
  rw [matrixAt,rosterAt]
  exact (decode_published_pin X G S b hp base v z).trans (densePin_read X G S b hp base v z)

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
