import OAI.Hierarchy.DescentResetSpanDispatch

namespace OAI
/-! # The three recorded range columns on the original physical node classes -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentSIMDLookup DescentDenseHostOrder DescentResetOperandSetup DescentResetPublicOperandBook
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "C" => a.successor.setup
local notation "r" => a.successor.middle.rootDepth
local notation "cfg" => publicOperands z roots menu.payload
variable {U : ℕ} (name : Fin U→Fin a.successor.setup.placement.sparse)
variable (Y : Fin (a.successor.setup.retained.outputs*a.successor.setup.placement.shapes)→Fin a.successor.setup.placement.oldHosts→
    Fin (a.successor.setup.placement.groups*a.successor.setup.placement.blocks)→Cell a.successor.setup.retained.bits)
variable (j : Fin a.successor.setup.retained.outputs) (block : Fin a.successor.setup.placement.blocks)
variable (host : Fin a.successor.setup.placement.newHosts) (g : Fin a.successor.setup.placement.groups)
local notation "table" => DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch
  menu.keep name Y j block
local notation "ret" => (((table) host g).val : Cell (C).fieldBits)
variable (x : (publicOperands z roots menu.payload).Data a.successor.middle.rotorBits) (index : Fin (publicOperands z roots menu.payload).mouths) (f : Fin 7)
local notation "pub" => (cfg).column z.board (C).fieldBits (some f) index x
local notation "reg" => (cfg).reg x
local notation "loc" => (finProdFinEquiv.symm index : Fin (cfg).args × Fin (cfg).nodes)
local notation "prv" => ((cfg).rotor.flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split
  (loc).2.val (loc).1.val f.succ (reg) : Cell (C).fieldBits)
variable (blank : ((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val=0 → ((publicOperands z roots menu.payload).reg x 1).val=0)
variable (physical : ∀hv : host.val<U,((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val≠0 →
    ((publicOperands z roots menu.payload).reg x 3).val=(a.successor.setup.placement.shape (name ⟨host.val,hv⟩)).val)
variable (shape : ↥(roster z.board a.successor.middle.rootDepth roots.Ht))
variable (live : ((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val≠0)
variable (seen : ((publicOperands z roots menu.payload).reg x 3).val=(localRank z.board a.successor.middle.rootDepth roots.Ht shape).val)
include live physical seen in
theorem newborn_slot (fresh : ∀key,shape.val≠.trunk false key) :
    ∀hv : host.val<U,menu.keep ((C).placement.shape (name ⟨host.val,hv⟩))=false :=by
  intro hv
  let id:=(C).placement.shape (name ⟨host.val,hv⟩)
  have actual : id.cast menu.nodes=ActorSetup.shapeIndex z.board r roots.Ht shape:=
    Fin.ext ((physical hv live).symm.trans seen)
  change (match ((ActorSetup.shapeIndex z.board r roots.Ht).symm (id.cast menu.nodes)).val with
    | .trunk false _=>true | _=>false)=false
  rw [actual,Equiv.symm_apply_apply]
  cases kind:shape.val with
  | good side seed cell=>rfl
  | fall side key position=>rfl
  | trunk side key=>cases side <;>simp_all

include live blank physical seen in
theorem relay_span_value {key} (relay : shape.val=.trunk true key) :
    menu.spanValue name Y j block host g x index f blank physical=pub :=by
  have fresh : ∀key₀,shape.val≠.trunk false key₀:=by simp [relay]
  have outside:=menu.newborn_slot name host x physical shape live seen fresh
  have eqn:=menu.spanValue_newborn name Y j block host g x index f blank physical outside
  have inactive : (cfg).rotor.flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split
      (loc).2.val (loc).1.val f.succ (reg)=0:=by
    unfold DescentRotorOperandQueryROM.Shape.flatReg
    split
    · rename_i active
      have raw : (⟨((reg) 3).val,active.2.2⟩ : Fin (roster z.board (cfg).rotor.residual (cfg).rotor.depth).card)=
          DescentResetTrunkPalette.order z.board (cfg).rotor.residual (cfg).rotor.depth shape:=Fin.ext seen
      let order := DescentResetTrunkPalette.order z.board (cfg).rotor.residual (cfg).rotor.depth
      have atShape : order.symm ⟨((reg) 3).val,active.2.2⟩ = shape :=
        (congrArg order.symm raw).trans (order.symm_apply_apply shape)
      have decoded : (order.symm ⟨((reg) 3).val,active.2.2⟩).val = .trunk true key :=
        (congrArg Subtype.val atShape).trans relay
      rw [decoded]
    · rfl
  apply Fin.ext
  simpa only [inactive,Nat.cast_zero,Fin.val_zero,zero_add] using eqn

include live blank physical seen in
theorem tree_span_value {side key pos} (tree : shape.val=.fall side key pos) :
    menu.spanValue name Y j block host g x index f blank physical=pub :=by
  have outside:=menu.newborn_slot name host x physical shape live seen (by simp [tree])
  have eqn:=menu.spanValue_newborn name Y j block host g x index f blank physical outside
  have inactive:=(cfg).rotor.flat_fallback z.board (reg) shape seen side key pos tree
    (cfg).multiplicity (cfg).grain (cfg).split (loc).2.val (loc).1.val f.succ
  apply Fin.ext
  simpa only [inactive,Nat.cast_zero,Fin.val_zero,zero_add] using eqn

include live blank physical seen in
theorem good_public_span_value {side seed site out} (good : shape.val=.good side seed site)
    (issued : (cfg).mixed z.board (loc).2.val (loc).1.val x=some out) :
    menu.spanValue name Y j block host g x index f blank physical=pub :=by
  have outside:=menu.newborn_slot name host x physical shape live seen (by simp [good])
  have eqn:=menu.spanValue_newborn name Y j block host g x index f blank physical outside
  have inactive:=(cfg).mixed_excludes_private z.board (loc).2.val (loc).1.val (cfg).split x out issued f.succ
  apply Fin.ext
  simpa only [inactive,Nat.cast_zero,Fin.val_zero,zero_add] using eqn

include live blank physical seen in
theorem good_private_span_value {side seed site} (good : shape.val=.good side seed site)
    (private_ : (cfg).rotor.flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split
      (loc).2.val (loc).1.val 0 (reg)≠0) :
    menu.spanValue name Y j block host g x index f blank physical=prv :=by
  have outside:=menu.newborn_slot name host x physical shape live seen (by simp [good])
  have eqn:=menu.spanValue_newborn name Y j block host g x index f blank physical outside
  have none_ : (cfg).mixed z.board (loc).2.val (loc).1.val x=none:=by
    cases received:(cfg).mixed z.board (loc).2.val (loc).1.val x with
    | none=>rfl
    | some v=>exact False.elim (private_ ((cfg).mixed_excludes_private z.board _ _ (cfg).split x v received 0))
  have off : pub=0:=by simp only [DescentResetPublicOperandBook.Config.column,none_]
  apply Fin.ext
  simpa only [off,Fin.val_zero,add_zero] using eqn

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
