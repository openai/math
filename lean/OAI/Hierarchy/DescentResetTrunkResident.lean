import OAI.Hierarchy.DescentResetTrunkPalette
import OAI.Hierarchy.DescentResetTrunkHostPointer

namespace OAI
/-! # A vacant receiver cannot borrow a populated relay stem -/
namespace Hierarchy.DescentResetTrunkPalette
open DescentCommonHost DescentDenseHostOrder DescentSixParty
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {H : ℕ}
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h) (r depth : ℕ)

local notation "colors" => roster board r depth
local notation "radix" => order board r depth

theorem inverse_side (x y : Fin (H*(colors).card)) (side : Bool) (hit : pointer board r depth side x=some y) :
    ∃s,pointer board r depth s y=some x:=by
  obtain ⟨⟨root,code⟩,rfl⟩:=finProdFinEquiv.surjective x
  obtain ⟨a,rfl⟩:=(radix).surjective code
  cases eqn : a.val with
  | good=>simp [pointer,flip,eqn,order] at hit
  | fall=>simp [pointer,flip,eqn,order] at hit
  | trunk s key=>
    let b : ↥colors:=⟨.trunk side key,flip_live board r depth a s side key eqn⟩
    have first:=at_label board r depth root a b side (by simp [eqn,flip,b])
    have label : ((radix) a)=localRank board r depth a:=rfl
    rw [label,first] at hit
    injection hit with hy
    subst y
    exact ⟨s,at_label board r depth root b a s (by simp [flip,b,eqn])⟩

end
end Hierarchy.DescentResetTrunkPalette
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "addresses" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))



local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) rawRank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "same" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables
local notation "key" => DescentOrderedReset.grains W B.count B.order


open DescentResetFieldAssembler DescentIssuedFallbackPanel DescentNextSignedWindow
local notation "rows" => blocks B
local notation "End" => (old).graph.Edge
local notation "Home" => (T).home
local notation "full" => totalLocal B
local notation "AC" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "before" => input.order.trans Fin.valEmbedding
local notation "half" => 2^(S.groupWidth k tail i+k-(T).commonDepth)*(2*(AC).cap)



open DescentPackedZip DescentSIMDLookup DescentResetTrunkIssue ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
local notation "Node₀" => Node (Z).V ((Z).V×DescentContacts.Endpoint (2^(Z).n)) (DescentCommonPalette.rotor (Z).graph).Site
local notation "short" t => DescentRelativeContacts.shortName (T).commonDepth ((T).code t)
local notation "high_" u => (addresses).symm ((u).1.1,(u).2)
local notation "hi_" t => DescentChosenRouter.coarseName (T).commonDepth ((T).code t)
local notation "touch" u t => ((rows).src (trunkParent B t)=u ∨ (rows).dst (trunkParent B t)=u)


local notation "rank" => (Z).rawHostRank T vertexCode


local notation "radius" => (Z).k-(T).commonDepth
local notation "depth_" => GroupStage.depthBound D n f g
local notation "shapeRank" => localRank (Z).graph radius depth_
local notation "roster_" => DescentDenseHostOrder.roster (Z).graph radius depth_

private theorem realized_terminal (v : B.next.V) (side : Bool) (z) (kind : v.val=.trunk side z) :
    ∃t : (Z).Fallback,(short t)=z:=by
  obtain ⟨a,_,eqn⟩:=Finset.mem_image.mp v.property
  have yes:=(Z).reset_occupied T (.trunk side z) ((Z).blockId T a)
  obtain ⟨t,hkey,_⟩:=yes.1 ⟨a,eqn.trans kind,rfl⟩
  exact ⟨t,hkey⟩


theorem trunk_alias_resident (h₀ : Fin (Fintype.card input.V*(roster_).card)) (v : B.next.V)
    (hit : DescentResetTrunkPalette.pointer (Z).graph radius depth_ true h₀=some (rank v)) :
    ∃u : B.next.V,rank u=h₀ :=by
  obtain ⟨s,back⟩:=DescentResetTrunkPalette.inverse_side (Z).graph radius depth_ _ _ true hit
  rw [trunk_pointer] at back
  cases found : trunkLabels B v with
  | none=>simp [found] at back
  | some p=>
    rw [found] at back
    cases s with
    | false => exact ⟨p.left,Option.some.inj back⟩
    | true => exact ⟨p.right,Option.some.inj back⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
