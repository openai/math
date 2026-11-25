import OAI.Hierarchy.DescentSiteTape
import OAI.Hierarchy.DescentGroupStageData

namespace OAI
/-! # The actual graph-site ordinal carried from its group, host row and block -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentColonies DescentSiteTape
open scoped Classical
noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k groups : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
variable (A : GroupStage W G q ε (Fin groups) V k) (vertex : V↪Fin (Fintype.card V))

def physicalPosition (u : W.graph.Site) : Fin (groups*Fintype.card V) := finProdFinEquiv ((A.pos u).1,vertex (A.pos u).2)

theorem physical_coordinates (coordinates : Function.Injective (fun v=>(A.pos v,A.block v))) :
    Function.Injective (fun u=>(physicalPosition A vertex u,A.block u)) := by
  intro u v eqn
  have h := finProdFinEquiv.injective (congrArg Prod.fst eqn)
  have groupEq : (A.pos u).1=(A.pos v).1 := congrArg (fun x : Fin groups × Fin (Fintype.card V) => x.1) h
  have hostEq : (A.pos u).2=(A.pos v).2 := vertex.injective (congrArg (fun x : Fin groups × Fin (Fintype.card V) => x.2) h)
  have blockEq : A.block u=A.block v := congrArg Prod.snd eqn
  exact coordinates (Prod.ext (Prod.ext groupEq hostEq) blockEq)

/-- The common public sparse footprint is groups times the host size times the radix. -/
def siteSlot (coordinates : Function.Injective (fun v=>(A.pos v,A.block v))) :
    W.graph.Site↪Fin ((groups*Fintype.card V)*2^k) :=
  ofCoordinates (physicalPosition A vertex) A.block (physical_coordinates A vertex coordinates)

def site (coordinates : Function.Injective (fun v=>(A.pos v,A.block v))) :
    W.graph.Site↪Fin (Fintype.card W.graph.Site) := (order (siteSlot A vertex coordinates)).toEmbedding

theorem siteSlot_val (coordinates : Function.Injective (fun v=>(A.pos v,A.block v))) (u : W.graph.Site) :
    (siteSlot A vertex coordinates u).val=
      ((A.pos u).1.val*Fintype.card V+(vertex (A.pos u).2).val)*2^k+(A.block u).val := by
  rw [siteSlot,coordinate_word]
  change ((vertex (A.pos u).2).val+Fintype.card V*(A.pos u).1.val)*2^k+(A.block u).val=_
  ring

theorem site_val (coordinates : Function.Injective (fun v=>(A.pos v,A.block v))) (u : W.graph.Site) :
    (site A vertex coordinates u).val=(Finset.univ.filter (fun v=>(siteSlot A vertex coordinates v).val<
      (siteSlot A vertex coordinates u).val)).card := order_val _ _

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
