import OAI.Hierarchy.DescentMountedRotorTransport

namespace OAI
/-! # The physical surface operand read on a realized exceptional tree -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentPhysicalSplit DescentResetGates DescentLaneGates DescentFallbackItemSelect
open DescentSIMDLookup DescentRetainedRangeDigits DescentBundleHistory DescentResetPublicOperandBook
open DescentResetOperandSetup DescentRotor DescentRouterSlots DescentBatchedNodeOrder
open DescentDenseHostOrder LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
open DescentChosenRouter DescentMixedRouter DescentBatchedBank DescentBaseProfile


def FallBadge {n d : ℕ} (board : NonlinearExpanders.Graph n d) (c : Config) (row : c.Data n) : Prop :=
  ∃s : ↥(roster board c.rotor.residual c.rotor.depth),
    (c.reg row 3).val=(localRank board c.rotor.residual c.rotor.depth s).val ∧
      ∃side key path,s.val=.fall side key path

theorem FallBadge.relabel_iff {n n' d d' : ℕ} {board : NonlinearExpanders.Graph n d}
    {after : NonlinearExpanders.Graph n' d'} {c c' : Config} (row : c.Data n)
    (config : c=c') (dim : n=n') (degree : d=d') (graph : HEq board after) :
    FallBadge board c row ↔ FallBadge after c' (Config.relabel config dim row) :=by
  subst c'
  subst n'
  subst d'
  cases eq_of_heq graph
  rfl

theorem header_relabel {n n' : ℕ} {c c' : Config} (row : c.Data n) (shape : c=c') (dim : n=n') (j : Fin 8) :
    (c'.oldConfig.header (c'.basic (Config.relabel shape dim row)) j).val=(c.oldConfig.header (c.basic row) j).val:=by
  subst c'
  subst n'
  rfl

variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "cfg" => publicOperands z roots menu.payload
local notation "C" => a.successor.setup
local notation "R" => (cfg).rotor
variable {U : ℕ} (name : Fin U→Fin a.successor.setup.placement.sparse)
    (Y : Fin (a.successor.setup.retained.outputs*a.successor.setup.placement.shapes)→Fin a.successor.setup.placement.oldHosts→
      Fin (a.successor.setup.placement.groups*a.successor.setup.placement.blocks)→Cell a.successor.setup.retained.bits)
    (j : Fin a.successor.setup.retained.outputs) (blk : Fin a.successor.setup.placement.blocks)
    (h : Fin a.successor.setup.placement.newHosts) (g : Fin a.successor.setup.placement.groups)
    (x : (publicOperands z roots menu.payload).Data a.successor.middle.rotorBits) (arg : Fin (publicOperands z roots menu.payload).args) (node : Fin (publicOperands z roots menu.payload).nodes)
    (blank : ((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val=0 → ((publicOperands z roots menu.payload).reg x 1).val=0)
    (physical : ∀hv : h.val<U,((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val≠0 →
      ((publicOperands z roots menu.payload).reg x 3).val=(a.successor.setup.placement.shape (name ⟨h.val,hv⟩)).val)
    (fresh : ∀hv : h.val<U,menu.keep (a.successor.setup.placement.shape (name ⟨h.val,hv⟩))=false)
local notation "mouth" => finProdFinEquiv (arg,node)
local notation "word" f:arg => menu.spanValue name Y j blk h g x mouth (page f) blank physical

set_option maxHeartbeats 650000 in
include blank physical in
theorem measured_fall_span {n' d' : ℕ} {after : NonlinearExpanders.Graph n' d'} {c' : Config}
    (shape : cfg=c') (dim : a.successor.middle.rotorBits=n') (degree : z.boardDegree=d') (board : HEq z.board after)
    (live : (c'.oldConfig.header (c'.basic (Config.relabel shape dim x)) 0).val≠0)
    (kind : FallBadge after c' (Config.relabel shape dim x)) (axis : Fin 3) :
    (word axis).val=(c'.column after (C).fieldBits (some (page axis))
      (finProdFinEquiv (arg.cast (congrArg (fun q : Config=>q.args) shape),
        node.cast (congrArg (fun q : Config=>q.nodes) shape))) (Config.relabel shape dim x)).val :=by
  obtain ⟨badge,ranked,side,t,path,tree⟩:=(FallBadge.relabel_iff x shape dim degree board).mpr kind
  have enabled : ((cfg).oldConfig.header ((cfg).basic x) 0).val≠0:=by
    simpa only [header_relabel x shape dim 0] using live
  rw [Config.column_relabel shape dim degree board]
  exact congrArg Fin.val (menu.tree_span_value name Y j blk h g x mouth (page axis) blank physical badge enabled ranked tree)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
