import OAI.Hierarchy.DescentExteriorPublished

namespace OAI
/-! # The terminal chart reads its physically published selected matrix -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory DescentGL DescentColonies DescentExterior
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
set_option quotPrecheck false
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height (initialGroup X S.copies (S.firstWidth G.b p))}
    {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0<p)

namespace NativeBranch
open PinCohorts DescentExteriorMatrixUpdate DescentExteriorShelf
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "E" => Fintype.card (Port P X.width)
variable (width : S.groupWidth k tail 0 + k = j + (j + rest))


/-- The genuine branch's selected matrix reaches all slabs on the same exterior input.
The upper public stream and both proposals pass unchanged through every date. -/
theorem published_layout {t bw : ℕ} (origin : ℕ) (cells : ℕ→Cell) (m : Memory bw)
    (x : Fin E→Plane j rest→Fin t→Bool) (z : Hidden E j rest t→Bool)
    (printed : Loaded origin (fun _=>LinearEquiv.refl _ _) x z m)
    (early : ∀i<S.length,(cells i).updated < origin)
    (inputs : b.path.matrixInputs base radix p hp _ (Chronology.seed_particles X (Chronology.epochsSource G r c)
      b.source (S.initialDigits radix) b.seed) b.recorded cells m)
    (startWord : m (cells 0).old.base=((matrixCode (Spine.start (active b.source base radix) (host b.source)).matrix).val:Computability.VPVNP.BurstRAM.Word bw))
    (join : ∀i<S.length,(cells i).updated=(cells (i+1)).old.base) :
    Loaded origin (publicLayout X G S b hp base width) x z (published j rest t E origin S.length cells m) :=
  published_loaded origin S.length cells m _ _ x z printed early
    (reached_layout X G S b hp base width cells m inputs startWord join)

end NativeBranch
end
end Hierarchy.DescentSixParty

end OAI
