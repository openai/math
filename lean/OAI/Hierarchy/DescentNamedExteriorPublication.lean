import OAI.Hierarchy.DescentNamedExteriorRows
import OAI.Hierarchy.DescentExteriorReelLayout

namespace OAI
/-! # Authentic published native matrix of a named epoch path -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory DescentGL DescentColonies DescentExterior
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
attribute [local irreducible] Origin.source
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
set_option quotPrecheck false
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S radix R r c) (hp : 0<p)

namespace Branch
open PinCohorts DescentExteriorMatrixUpdate DescentExteriorShelf
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "shape" => j+(j+rest)
local notation "E" => Fintype.card (Port P X.width)
variable (width : S.groupWidth k tail 0 + k = j + (j + rest))

theorem issued_layout (slab:Fin E) :
    (matrixCode (publicLayout X G S b hp base width slab)).val=
      (matrixCode (Branch.pinSpine X G S b hp base).matrix).val := by
  have eqn:=reprinted_matrix (Branch.pinSpine X G S b hp base) (publicSpine X G S b hp base width) width rfl
  have value:=congrArg (fun L:Layout shape=>(matrixCode L).val) eqn
  change (matrixCode ((LinearEquiv.refl _ _).trans (publicSpine X G S b hp base width).matrix)).val=_
  rw [LinearEquiv.refl_trans]
  exact value.trans (retag_code width _)

theorem reached_layout {bw:ℕ} (cells:ℕ→Cell) (m:Memory bw)
    (inputs:b.path.matrixInputs base radix p hp _ b.origin.particles b.recorded cells m)
    (startWord:m (cells 0).old.base=((matrixCode (Spine.start (active b.origin.source base radix) (host b.origin.source)).matrix).val:Computability.VPVNP.BurstRAM.Word bw))
    (join:∀t<S.length,(cells t).updated=(cells (t+1)).old.base) (slab:Fin E) :
    DescentExteriorMatrixUpdate.reached cells m S.length (cells S.length).old.base=((matrixCode (publicLayout X G S b hp base width slab)).val:Computability.VPVNP.BurstRAM.Word bw) := by
  rw [issued_layout X G S b hp base width slab]
  exact b.path.matrix_read base radix p hp _ _ b.recorded cells m inputs startWord join

/-- The genuine branch's selected matrix reaches all slabs on the same exterior input.
The upper public stream and both proposals pass unchanged through every date. -/
theorem published_layout {t bw : ℕ} (origin : ℕ) (cells : ℕ→Cell) (m : Memory bw)
    (x : Fin E→Plane j rest→Fin t→Bool) (z : Hidden E j rest t→Bool)
    (printed : Loaded origin (fun _=>LinearEquiv.refl _ _) x z m)
    (early : ∀i<S.length,(cells i).updated < origin)
    (inputs : b.path.matrixInputs base radix p hp _ b.origin.particles b.recorded cells m)
    (startWord : m (cells 0).old.base=((matrixCode (Spine.start (active b.origin.source base radix) (host b.origin.source)).matrix).val:Computability.VPVNP.BurstRAM.Word bw))
    (join : ∀i<S.length,(cells i).updated=(cells (i+1)).old.base) :
    Loaded origin (publicLayout X G S b hp base width) x z (published j rest t E origin S.length cells m) :=
  published_loaded origin S.length cells m _ _ x z printed early
    (reached_layout X G S b hp base width cells m inputs startWord join)

/-- The selected local ordinary and reset codes determine the physical terminal shelf.
All other fields of the cumulative scan are the publicly computed calendar and its literal start. -/
theorem reel_layout {t bw : ℕ} (origin fence : ℕ) (plan : Reel) (m : Memory bw)
    (x : Fin E→Plane j rest→Fin t→Bool) (z : Hidden E j rest t→Bool)
    (printed : Loaded origin (fun _=>LinearEquiv.refl _ _) x z m)
    (entries : b.path.savedRotations plan fence tail m)
    (geometry : plan.Room bw initialBits S.length fence origin) :
    Loaded origin (publicLayout X G S b hp base width) x z
      (plan.result j rest t E initialBits S.length origin m) := by
  let prior:=initialized (plan.old 0) initialBits m
  have boot:=«initialize» (plan.old 0) initialBits m geometry.startFit
  have held : b.path.savedRotations plan fence tail prior:=
    b.path.savedRotations_move plan fence entries (fun a ha=>boot.2.2.2 a (by have:=geometry.boot;omega))
  have physical:=b.path.matrixInputs_of_saved plan fence base radix p hp _
    b.origin.particles
    b.recorded prior held geometry.retained
  apply published_layout X G S b hp base width origin (plan.cells initialBits) prior x z _ geometry.high physical _ geometry.join
  · intro col u live
    have neq : plan.old 0 ≠ (bank j rest t E origin col.val).base+u:=by
      change plan.old 0 ≠ origin+col.val*span j rest t E+u
      have :=geometry.startLow
      omega
    exact (boot.2.2.2 _ neq).trans (printed col u live)
  · change initialized (plan.old 0) initialBits m (plan.old 0)=_
    simpa only [initialCode_eq (active b.origin.source base radix) (host b.origin.source)] using boot.2.2.1

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

-- Keep branch projections opaque while Lean indexes these theorem signatures.
open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Branch.pinSpine Branch.publicSpine Branch.publicLayout
