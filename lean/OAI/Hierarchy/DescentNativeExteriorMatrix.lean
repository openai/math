import OAI.Hierarchy.DescentNativeExteriorRows
import OAI.Hierarchy.DescentExteriorMatrixPath

namespace OAI
/-! # The branch's physical cumulative matrix is its one three-flight exterior rotation -/

namespace Hierarchy.DescentExterior
open DescentGL DescentColonies Computability.VPVNP.BurstRAM
noncomputable section
private theorem store_cast {b f a c:ℕ} (u:b+f=a) (v:b+f=c) (eq:a=c) (x:Bits b×Bits f) :
    castBits eq (Spine.store u x)=Spine.store v x := by cases eq; rfl
def retagMatrix {a c:ℕ} (eq:a=c) (L:Layout a) : Layout c := ((castBits eq).symm.trans L).trans (castBits eq)
theorem retag_code {a c:ℕ} (eq:a=c) (L:Layout a) :
    (matrixCode (retagMatrix eq L)).val=(matrixCode L).val := by
  subst c
  congr 2

theorem reprinted_matrix {P E O V:Type} {b f a c:ℕ} {raw:P→Bits a} {act:P→Bits b}
    {src:P→O} {dst:P→V} {pub:E→Bits c} {act':E→Bits b} {src':E→O} {dst':E→V}
    (r:Spine raw act src dst f) (s:Spine pub act' src' dst' f) (eq:a=c)
    (cut:s.cut=(castBits eq.symm).trans r.cut) :
    s.matrix=retagMatrix eq r.matrix := by
  ext x i
  change (Spine.store s.width (s.cut x)) i=(castBits eq (Spine.store r.width (r.cut ((castBits eq).symm x)))) i
  rw [store_cast r.width s.width eq]
  subst c
  rw [cut];rfl
end
end Hierarchy.DescentExterior

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
open PinCohorts DescentExteriorMatrixUpdate
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
local notation "shape" => j+(j+rest)
local notation "E" => Fintype.card (Port P X.width)
variable (width : S.groupWidth k tail 0 + k = j + (j + rest))

theorem issued_layout (slab:Fin E) :
    (matrixCode (publicLayout X G S b hp base width slab)).val=
      (matrixCode (b.pinSpine X G S hp base).matrix).val := by
  have eqn:=reprinted_matrix (b.pinSpine X G S hp base) (publicSpine X G S b hp base width) width rfl
  have value:=congrArg (fun L:Layout shape=>(matrixCode L).val) eqn
  change (matrixCode ((LinearEquiv.refl _ _).trans (publicSpine X G S b hp base width).matrix)).val=_
  rw [LinearEquiv.refl_trans]
  exact value.trans (retag_code width _)

theorem reached_layout {bw:ℕ} (cells:ℕ→Cell) (m:Memory bw)
    (inputs:b.path.matrixInputs base radix p hp _ (Chronology.seed_particles X (Chronology.epochsSource G r c)
      b.source (S.initialDigits radix) b.seed) b.recorded cells m)
    (startWord:m (cells 0).old.base=((matrixCode (Spine.start (active b.source base radix) (host b.source)).matrix).val:Computability.VPVNP.BurstRAM.Word bw))
    (join:∀t<S.length,(cells t).updated=(cells (t+1)).old.base) (slab:Fin E) :
    reached cells m S.length (cells S.length).old.base=((matrixCode (publicLayout X G S b hp base width slab)).val:Computability.VPVNP.BurstRAM.Word bw) := by
  rw [issued_layout X G S b hp base width slab]
  exact b.path.matrix_read base radix p hp _ _ b.recorded cells m inputs startWord join

end NativeBranch
end
end Hierarchy.DescentSixParty

end OAI
