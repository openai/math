import OAI.Hierarchy.DescentResetRetainedDimensions
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentDatedNodeMetadataChart
import OAI.Hierarchy.DescentPreviousOperandLayout

namespace OAI
/-! # Complete original input directory for a reset of the retained operand registers -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOperandStateBanks ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (v : Layout)

def previousChart : DescentDatedNodeMetadata.Chart :=
  ⟨v.blocks,v.previousNodes,v.hosts,v.groups,v.bits,v.previousLanes⟩

def previousLayout : DescentDatedPriorOperand.Layout :=
  ⟨v.blocks,v.previousNodes,v.previousArgs,v.hosts,v.groups,v.previousLanes,v.bits-2⟩

def directory {α : Type*} (metadata : Fin 2→Fin v.blocks→α) (pages : Pages v.previousArgs→Fin v.blocks→α)
    (j : Fin v.sources) : α:=
  let key : Fin v.fields×Fin v.blocks:=finProdFinEquiv.symm j
  if h:key.1.val<2 then metadata ⟨_,h⟩ key.2 else
    pages ⟨key.1.val-2,by have hk:=key.1.isLt;change _<2+7*v.previousArgs at hk;omega⟩ key.2

/-- The seven original properties stay in their public field/argument-major, block-minor address order. -/
def priorBanks (primitive : Fin 2→Fin v.blocks→Bank) (operands : ℕ) : Fin v.sources→Bank :=
  v.directory primitive (fun p x=>DescentDatedPriorOperand.previousBank v.previousLayout operands x p)

def seedPrior (metadata operands : ℕ) :=v.priorBanks (v.previousChart.seedBank metadata) operands
def laterPrior (metadata operands : ℕ) :=v.priorBanks (v.previousChart.bank metadata) operands

theorem directory_property {α : Type*} (metadata : Fin 2→Fin v.blocks→α) (pg : Pages v.previousArgs→Fin v.blocks→α)
    (f : Fin 7) (arg : Fin v.previousArgs) (x : Fin v.blocks) :
    v.directory metadata pg (v.sourceID (v.operandField f arg) x)=pg (page f arg) x :=by
  classical
  simp only [directory,sourceID,Equiv.symm_apply_apply,operandField]
  have h : ¬2+(finProdFinEquiv (f,arg)).val<2:=by omega
  rw [dite_eq_right h]
  apply congrArg (fun q : Pages v.previousArgs=>pg q x)
  apply Fin.ext
  change 2+(finProdFinEquiv (f,arg)).val-2=(finProdFinEquiv (f,arg)).val
  omega

theorem directory_role {α : Type*} (metadata : Fin 2→Fin v.blocks→α) (pg : Pages v.previousArgs→Fin v.blocks→α) (x : Fin v.blocks) :
    v.directory metadata pg (v.sourceID v.occupiedField x)=metadata 0 x ∧ v.directory metadata pg (v.sourceID v.arityField x)=metadata 1 x :=by
  simp [directory,sourceID,occupiedField,arityField]

/-- Native source obligations for all prior pages from their two true primitive and seven pointer banks.
Every physical address is determined by the preceding stage's two output floors. -/
theorem priorIssued (floor operands : ℕ) (m : Memory w) (metadata : Fin 2→Fin v.blocks→Bank)
    (role : Fin 2→Fin v.blocks→Fin v.hosts→Fin v.groups→Cell v.wholeWord)
    (X : Pages v.previousArgs→Fin v.blocks→Fin v.hosts→Fin v.groups→Cell v.wholeWord)
    (mfit : ∀f x,(metadata f x).Fits w floor ∧ v.previousLayout.rows≤(metadata f x).size)
    (pfit : ∀p x,(DescentDatedPriorOperand.previousBank v.previousLayout operands x p).Fits w floor ∧
      v.previousLayout.rows≤(DescentDatedPriorOperand.previousBank v.previousLayout operands x p).size)
    (md : ∀f x,Reads (metadata f x) (role f x) v.previousLanes m)
    (pg : ∀p x,Reads (DescentDatedPriorOperand.previousBank v.previousLayout operands x p) (X p x) v.previousLanes m) :
    ∀j,(v.priorBanks metadata operands j).Fits w floor ∧ v.hosts*chunks v.groups v.previousLanes≤(v.priorBanks metadata operands j).size ∧
      Reads (v.priorBanks metadata operands j) (v.directory role X j) v.previousLanes m :=by
  intro j
  unfold priorBanks directory
  dsimp only
  split
  · exact ⟨(mfit ..).1,(mfit ..).2,md _ _⟩
  · exact ⟨(pfit ..).1,(pfit ..).2,pg _ _⟩

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
