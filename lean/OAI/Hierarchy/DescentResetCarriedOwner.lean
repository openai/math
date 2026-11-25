import OAI.Hierarchy.DescentRetainedCorrectionGate
import OAI.Hierarchy.DescentResetSpanDispatch
import OAI.Hierarchy.DescentSelectedOperandColumns

namespace OAI
/-! All packed selectors use the same compact actor that supplied the carried tag. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentSIMDLookup DescentDenseHostOrder DescentResetOperandSetup DescentResetPublicOperandBook
open scoped Classical Fin.CommRing
noncomputable section
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
set_option quotPrecheck false
local notation "C" => a.successor.setup
local notation "r" => a.successor.middle.rootDepth
local notation "cfg" => publicOperands z roots menu.payload
variable {U : ℕ} (name : Fin U→Fin a.successor.setup.placement.sparse)
variable (host : Fin a.successor.setup.placement.newHosts)
variable (x : (publicOperands z roots menu.payload).Data a.successor.middle.rotorBits) (index : Fin (publicOperands z roots menu.payload).mouths)
variable (width : ℕ) (field : Option (Fin 7)) (digit : Fin 8)
local notation "pub" => (cfg).column z.board width field index x
local notation "reg" => (cfg).reg x
local notation "loc" => (finProdFinEquiv.symm index : Fin (cfg).args × Fin (cfg).nodes)
local notation "prv" => ((cfg).rotor.flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split
  (loc).2.val (loc).1.val digit (reg) : Cell width)
variable (blank : ((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val=0 → (((publicOperands z roots menu.payload).reg x) 1).val=0)
variable (physical : ∀hv : host.val<U,((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val≠0 →
    (((publicOperands z roots menu.payload).reg x) 3).val=(a.successor.setup.placement.shape (name ⟨host.val,hv⟩)).val)

include blank physical in
theorem private_public_off (hU : host.val<U) (present : menu.keep ((C).placement.shape (name ⟨host.val,hU⟩))=true) :
    (prv)=0 ∧ (pub)=0 := by
  by_cases empty_ : ((cfg).oldConfig.header ((cfg).basic x) 0).val=0
  · have pv : (cfg).rotor.flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split
        (loc).2.val (loc).1.val digit (reg)=0:=by
      simp [DescentRotorOperandQueryROM.Shape.flatReg,blank empty_]
    have pb : (cfg).mixed z.board (loc).2.val (loc).1.val x=none:=by
      simp [DescentResetPublicOperandBook.Config.mixed,empty_]
    exact ⟨by simp only [pv,Nat.cast_zero],by simp only [DescentResetPublicOperandBook.Config.column,pb]⟩
  let id:=((C).placement.shape (name ⟨host.val,hU⟩))
  let sh:=(ActorSetup.shapeIndex z.board r roots.Ht).symm (id.cast menu.nodes)
  have primary : ∃key,sh.val=.trunk false key:=by
    change (match sh.val with | .trunk false _=>true | _=>false)=true at present
    cases body : sh.val with
    | trunk side key=>cases side <;>simp_all
    | good side seed cell=>simp [body] at present
    | fall side key digits=>simp [body] at present
  have same : ((reg) 3).val=(localRank z.board r roots.Ht sh).val:=by
    calc
      _=id.val:=physical hU empty_
      _=((ActorSetup.shapeIndex z.board r roots.Ht) sh).val:=
        (congrArg Fin.val ((ActorSetup.shapeIndex z.board r roots.Ht).apply_symm_apply (id.cast menu.nodes))).symm
  have pv:=(cfg).rotor.flat_primary z.board (reg) sh same primary (cfg).multiplicity (cfg).grain
    (cfg).split (loc).2.val (loc).1.val digit
  exact ⟨by simp only [pv,Nat.cast_zero],(cfg).primary_column z.board x sh same primary _ _ _⟩


variable (Y : Fin (a.successor.setup.retained.outputs*a.successor.setup.placement.shapes)→Fin a.successor.setup.placement.oldHosts→
    Fin (a.successor.setup.placement.groups*a.successor.setup.placement.blocks)→Cell a.successor.setup.retained.bits)
variable (j : Fin a.successor.setup.retained.outputs) (block : Fin a.successor.setup.placement.blocks) (g : Fin a.successor.setup.placement.groups)
local notation "tag" => ((DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch
  menu.keep name Y j block host g).val : Cell (C).fieldBits)
include blank physical in
theorem carried_gate («on» : (tag).val=1) : (prv)=0 ∧ (pub)=0:=by
  by_cases hv:host.val<U
  · by_cases keep:menu.keep ((C).placement.shape (name ⟨host.val,hv⟩))=true
    · exact menu.private_public_off name host x index width field digit blank physical hv keep
    · simp [DescentRetainedTargetPlacement.Chart.compact,DescentResetDenseOperand.dense,hv,
        DescentRetainedTargetPlacement.Chart.selected,keep] at «on»
  · simp [DescentRetainedTargetPlacement.Chart.compact,DescentResetDenseOperand.dense,hv] at «on»

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
