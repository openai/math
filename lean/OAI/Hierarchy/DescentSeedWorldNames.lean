import OAI.Hierarchy.DescentReached
import OAI.Hierarchy.DescentNamedPlacement
import OAI.Hierarchy.DescentDensePhysicalOrder

namespace OAI
/-! # Start the first nonlinear ordinary choice on the numbered physical seed graph

Both permutations are proof-level changes of network coordinates. Mutable registers continue to
use the old physical host, block and cable ordinals. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentPacking DescentStageEdgeReceipt DescentPhysicalOrder
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist : ℕ}
    (R : Reached W G q ε S k i z D wire hist)
local notation "A" => R.placement

def site := DescentPhysicalOrder.rename (((A).site R.vertex R.valid.coordinates).trans Fin.valEmbedding)
def edge := DescentPhysicalOrder.rename (R.order.trans Fin.valEmbedding)
def world := PhysicalRename.world W (site R) (edge R)
def placed := (A).names (site R) (edge R)

theorem site_code (v : W.graph.Site) :
    originalId (world R).graph.Site (site R v)=((A).site R.vertex R.valid.coordinates v).val :=
  (congrArg Fin.val (DescentPhysicalOrder.code_rename _ v)).trans
    (congrArg Fin.val (GroupStage.compact_dense ((A).site R.vertex R.valid.coordinates) v))

theorem edge_code (e : W.graph.Edge) :
    originalId (world R).graph.Edge (edge R e)=(R.order e).val :=
  (congrArg Fin.val (DescentPhysicalOrder.code_rename _ e)).trans
    (congrArg Fin.val (GroupStage.compact_dense R.order e))

theorem coordinates : Function.Injective (fun v=>((placed R).pos v,(placed R).block v)) :=
  GroupStage.names_coordinates (A) (site R) (edge R) R.valid.coordinates

theorem bounds : (placed R).StateBounds S i := by
  refine ⟨coordinates R,R.valid.host,R.valid.capacity,R.valid.bundleCapacity,?_,R.valid.atom,
    R.valid.valuation,R.valid.paidUnit,?_⟩
  · have sum_ : (∑v,((placed R).records v).length)=∑v,((A).records v).length :=
      ((site R).symm.sum_comp (fun v=>((A).records v).length))
    rw [sum_];exact R.valid.history
  · intro e
    exact R.valid.divides ((edge R).symm e)

theorem site_at (v : W.graph.Site) :
    ((placed R).site R.vertex (coordinates R) (site R v)).val=((A).site R.vertex R.valid.coordinates v).val := by
  have slot (u : W.graph.Site) :
      ((placed R).siteSlot R.vertex (coordinates R) (site R u)).val =
        ((A).siteSlot R.vertex R.valid.coordinates u).val := by
    refine ((placed R).siteSlot_val R.vertex (coordinates R) (site R u)).trans ?_
    refine Eq.trans ?_ ((A).siteSlot_val R.vertex R.valid.coordinates u).symm
    exact congrArg (fun t : W.graph.Site =>
      (((A).pos t).1.val * Fintype.card R.V + (R.vertex ((A).pos t).2).val) * 2^k + ((A).block t).val)
      ((site R).symm_apply_apply u)
  refine ((placed R).site_val R.vertex (coordinates R) (site R v)).trans ?_
  refine Eq.trans ?_ ((A).site_val R.vertex R.valid.coordinates v).symm
  symm
  apply Finset.card_bij (fun t _=>site R t)
  · intro t ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_of_eq_of_lt (slot t) (lt_of_lt_of_eq (Finset.mem_filter.mp ht).2 (slot v).symm)⟩
  · exact fun _ _ _ _ eqn=>(site R).injective eqn
  · intro t ht
    obtain ⟨u,rfl⟩:=(site R).surjective t
    exact ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_of_eq_of_lt (slot u).symm (lt_of_lt_of_eq (Finset.mem_filter.mp ht).2 (slot v))⟩,rfl⟩

def reached : Reached (world R) G q ε S k i z D wire hist where
  V:=R.V
  placement:=placed R
  valid:=bounds R
  grain:=R.grain
  edges:=R.edges
  atoms:=R.atoms
  branch:=R.branch
  order:=(edge R).symm.toEmbedding.trans R.order
  vertex:=R.vertex
  edgeName _ v:=by
    obtain ⟨e,rfl⟩:=(edge R).surjective v
    exact (edge_code R e).trans (congrArg (fun t=>(R.order t).val) ((edge R).symm_apply_apply e).symm)
  siteName _ v:=by obtain ⟨u,rfl⟩:=(site R).surjective v;exact (site_code R u).trans (site_at R u).symm

theorem valuation : (world R).value=W.value := PhysicalRename.value W (site R) (edge R)

theorem position (v : W.graph.Site) :
    (placed R).pos (site R v)=(A).pos v ∧ (placed R).block (site R v)=(A).block v ∧
    (placed R).records (site R v)=(A).records v := by
  exact ⟨congrArg (A).pos ((site R).symm_apply_apply v),congrArg (A).block ((site R).symm_apply_apply v),
    congrArg (A).records ((site R).symm_apply_apply v)⟩

theorem cable (e : W.graph.Edge) :
    (world R).graph.src (edge R e)=site R (W.graph.src e) ∧
    (world R).graph.dst (edge R e)=site R (W.graph.dst e) ∧
    (world R).graph.width (edge R e)=W.graph.width e ∧
    ((reached R).order (edge R e)).val=(R.order e).val := by
  exact ⟨PhysicalRename.src W.graph (site R) (edge R) e,PhysicalRename.dst W.graph (site R) (edge R) e,
    PhysicalRename.width W.graph (site R) (edge R) e,congrArg (fun t=>(R.order t).val) ((edge R).symm_apply_apply e)⟩

theorem attached (p : P) : (world R).graph.attach p=site R (W.graph.attach p) := rfl

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
