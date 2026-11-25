import OAI.Hierarchy.DescentResetOriginRank
import OAI.Hierarchy.DescentResetTrunkOperandPrefix

namespace OAI
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentPrimitivePalette DescentLocalArchiveOrder DescentResetTrunks Chronology
open DescentCompiler DescentColonies DescentStageEdgeReceipt Computability.BorderVNP.Crossing ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset cap ctl) (hp : 0<p) (whole : p∣B.reset.unit) (a : Archive W)
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "unit" => B.reset.unit/p
local notation "splitEq" => ((Nat.div_mul_cancel whole).symm : B.reset.unit=unit*p)
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "raw_" => W.granular B.count (z*G.b) B.fit
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans cap.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "where_" x => resetOrigin B hp whole a x
local notation "loc_" => fun e : (raw_).graph.Edge=>B.terminals.home ((raw_).graph.dst e)

/-- Undoing the stage's site renaming gives the recorded owner of this very
archived node, before splitting the marked cables. -/
theorem original_operand_site (x : NodeOrder.All next_) :
    (hop).symm x.1=chosenOwner B hp whole a (where_ x) :=by
  have site:=reached_node_site B hp whole a x
  change (hop) (chosenOwner B hp whole a (where_ x))=x.1 at site
  exact (hop).symm_apply_eq.mpr site.symm

/-- The relay node of an original incoming grain is at the target of the
corresponding trunk. -/
theorem relay_original_site (x : NodeOrder.All next_) (e : (raw_).graph.Edge)
    (origin : (where_ x)=Sum.inr (.inl e)) :
    (hop).symm x.1=(coarse).graph.dst (trunkParent B (loc_ e)) :=by
  rw [original_operand_site B hp whole a x,origin]
  apply (B.reset.resetNames B.terminals).injective
  change (B.reset.resetNames B.terminals) ((B.reset.resetNames B.terminals).symm (.inl (true,loc_ e)))=_
  rw [Equiv.apply_symm_apply]
  exact (trunk_nodes B (loc_ e)).2.symm

/-- The other relay half at this same site reads the source of the incoming stem. -/
theorem relay_original_stem (x : NodeOrder.All next_) (e : (raw_).graph.Edge)
    (origin : (where_ x)=Sum.inr (.inl e)) :
    (hop).symm x.1=(coarse).graph.src (stemParent B (true,e)) :=by
  rw [original_operand_site B hp whole a x,origin]
  apply (B.reset.resetNames B.terminals).injective
  change (B.reset.resetNames B.terminals) ((B.reset.resetNames B.terminals).symm (.inl (true,loc_ e)))=_
  rw [Equiv.apply_symm_apply]
  exact (stem_nodes B true e).1.symm

/-- The gate's own bank actor fixes its actual site in the coarse graph. -/
theorem device_original_site (x : NodeOrder.All next_) (v : B.reset.bank.Site)
    (u : (B.reset.laneRecipe birth unit p hp splitEq v).Node) (origin : (where_ x)=Sum.inr (.inr ⟨v,u⟩)) :
    (hop).symm x.1=(B.reset.resetNames B.terminals).symm (.inr v) :=by
  rw [original_operand_site B hp whole a x,origin]
  rfl

theorem device_wire_original_site (x : NodeOrder.All next_) (v : B.reset.bank.Site)
    (u : (B.reset.laneRecipe birth unit p hp splitEq v).Node) (origin : (where_ x)=Sum.inr (.inr ⟨v,u⟩))
    (edge : B.reset.bank.Edge) (side : Bool) (atEnd : (if side then B.reset.bank.dst edge else B.reset.bank.src edge)=v) :
    let parent:=(motherNames B).symm (.inr (.inr edge))
    (hop).symm x.1=if side then (coarse).graph.dst parent else (coarse).graph.src parent :=by
  intro parent
  let same:=funext (fun e=>(B.reset.allWidths e).symm)
  have header:=sourceFields_read raw_ B.terminals.home B.reset.placement.input B.terminals.hub same
    B.reset.bank B.reset.tables parent
  change physicalFields _ _ _ _ _ _ _ parent=sourceFields _ _ _ _ _
    ((motherNames B) ((motherNames B).symm (.inr (.inr edge)))) at header
  rw [Equiv.apply_symm_apply] at header
  rw [device_original_site B hp whole a x v u origin]
  apply (B.reset.resetNames B.terminals).injective
  rw [Equiv.apply_symm_apply]
  cases side
  · change B.reset.bank.src edge=v at atEnd
    exact (congrArg Sum.inr atEnd.symm).trans (congrArg RawFields.src header).symm
  · change B.reset.bank.dst edge=v at atEnd
    exact (congrArg Sum.inr atEnd.symm).trans (congrArg RawFields.dst header).symm

theorem device_socket_original_site (x : NodeOrder.All next_) (v : B.reset.bank.Site)
    (u : (B.reset.laneRecipe birth unit p hp splitEq v).Node) (origin : (where_ x)=Sum.inr (.inr ⟨v,u⟩))
    (socket : Attached B.reset.bank v) (e : (raw_).graph.Edge)
    (inFibre : B.reset.placement.input socket.val.1 e=socket.val.2) :
    (hop).symm x.1=(coarse).graph.dst (stemParent B (socket.val.1,e)) :=by
  rw [device_original_site B hp whole a x v u origin]
  apply (B.reset.resetNames B.terminals).injective
  rw [Equiv.apply_symm_apply]
  have dst:=(stem_nodes B socket.val.1 e).2.1
  rw [inFibre] at dst
  exact (congrArg Sum.inr socket.property.symm).trans dst.symm

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
