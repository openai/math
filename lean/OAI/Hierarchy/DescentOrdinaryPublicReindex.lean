import OAI.Hierarchy.DescentReachedTransportPublic
import OAI.Hierarchy.DescentReachedSourceOperand

namespace OAI
/-! Reindex the actual occupied bit-recipe slot along the selected-world equality
and the genuine normalization equality, retaining the original source node. -/
namespace Hierarchy.DescentBundleHistory.Normalized
open DescentSixParty DescentKernelHistory DescentStageEdgeReceipt DescentCompiler Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p shapes grain : ℕ} {bits : P→ℕ}
    {X Y : MarkedWorld F d P bits} {n : Normalize X} {m : Normalize Y}
    (input : X=Y) (same : HEq n m) (B : BitDescription Y)
local notation "before" => cast (congrArg BitDescription input.symm) B
local notation "old" => NodeOrder.All ((before).follow n)
local notation "new₁" => NodeOrder.All (B.follow m)
include same in
def namedNode (x : old) : new₁ :=by subst Y;obtain rfl:=eq_of_heq same;exact x

theorem fin_number {a b : ℕ} {i : Fin a} {j : Fin b} (valid : a=b) (same : HEq i j) : i.val=j.val :=by
  subst b;obtain rfl:=eq_of_heq same;rfl

theorem named_root (x : old) :
    NodeOrder.followNames m B (namedNode input same B x)=
      NodeOrder.castNames input.symm B (NodeOrder.followNames n before x) :=by
  subst Y;obtain rfl:=eq_of_heq same;rfl

local notation:max "right" x:arg => namedNode input same B x

def namedIncident (x : old) (e : Incident n.result.graph x.1) : Incident m.result.graph (right x).1 :=by
  subst Y;obtain rfl:=eq_of_heq same;exact e

theorem named_width (x : old) (e : Incident n.result.graph x.1) :
    n.result.graph.width e.val=m.result.graph.width (namedIncident input same B x e).val :=by
  subst Y;obtain rfl:=eq_of_heq same;rfl

variable (hp : 0<p) (pos : 0<grain) (whole : p∣grain)
    (sh : WorldShape p shapes B) (cuts : Normalize.CutsEqual grain n) (cuts' : Normalize.CutsEqual grain m)
local notation "prior" => WorldShape.follow hp pos whole n cuts (sh.transport input.symm)
local notation "result" => WorldShape.follow hp pos whole m cuts' sh
local notation:max "need" x:arg => (((prior).sites (x).1).recipe hp).arity (x).2
local notation:max "have_" x:arg => (((result).sites (right x).1).recipe hp).arity (right x).2

theorem named_arity (x : old) : need x=have_ x :=by subst Y;obtain rfl:=eq_of_heq same;rfl

theorem named_read (x : old) (j : Fin (need x)) (edge : Incident n.result.graph x.1) (lo : ℕ)
    (fits : (lo+1)*p≤n.result.graph.width edge.val)
    (hit : (((prior).sites x.1).recipe hp).operand x.2 j=.inl ⟨.inl edge,lo,fits⟩) :
    (((result).sites (right x).1).recipe hp).operand (right x).2
      (j.cast (named_arity input same B hp pos whole sh cuts cuts' x))=
        .inl ⟨.inl (namedIncident input same B x edge),lo,fits.trans_eq (named_width input same B x edge)⟩ :=by
  subst Y;obtain rfl:=eq_of_heq same;exact hit

variable {S : AtomSchedule} {G : PoweredGadget F} {k age z degree wire hist : ℕ} {price ε : ℝ}
    (reached : Reached n.result G price ε S k age z degree wire hist)
    (eqn : n.result=m.result)
theorem named_pointer (x : old) (edge : Incident n.result.graph x.1) (lo : ℕ) (fit : (lo+1)*p≤n.result.graph.width edge.val) :
    reached.firstCable hp (Reached.originalSite eqn (right x).1)
        (Reached.originalIncident eqn (right x).1 (namedIncident input same B x edge)) lo
        (Reached.original_fit eqn (right x).1 (namedIncident input same B x edge) lo (fit.trans_eq (named_width input same B x edge)))=
      reached.firstCable hp x.1 edge lo fit :=by
  subst Y;obtain rfl:=eq_of_heq same;rfl

theorem named_site (x : old) : Reached.originalSite eqn (right x).1=x.1 :=by
  subst Y;obtain rfl:=eq_of_heq same;rfl

include input same in
theorem named_result : n.result=m.result :=by subst Y;obtain rfl:=eq_of_heq same;rfl

variable {Z : MarkedWorld F d P bits} (other : Reached Z G price ε S k age z degree wire hist)
    (arrived : HEq reached other) (diagram : Z=m.result)
local notation:max "modelSite" x:arg => Reached.originalSite diagram (right x).1

include arrived in
theorem reached_coords (x : old) :
    ((other.vertex (other.placement.pos (modelSite x)).2).val,(other.placement.pos (modelSite x)).1.val,
      (other.placement.block (modelSite x)).val)=
    ((reached.vertex (reached.placement.pos x.1).2).val,(reached.placement.pos x.1).1.val,
      (reached.placement.block x.1).val) :=by
  have g:n.result=Z:=(named_result input same).trans diagram.symm
  cases g;obtain rfl:=eq_of_heq arrived
  rw [named_site input same B diagram x]

include arrived in
theorem reached_pointer (x : old) (edge : Incident n.result.graph x.1) (lo : ℕ)
    (fit : (lo+1)*p≤n.result.graph.width edge.val) :
    other.firstCable hp (modelSite x) (Reached.originalIncident diagram (right x).1 (namedIncident input same B x edge))
        lo (Reached.original_fit diagram (right x).1 (namedIncident input same B x edge) lo (fit.trans_eq (named_width input same B x edge)))=
      reached.firstCable hp x.1 edge lo fit :=by
  have g:n.result=Z:=(named_result input same).trans diagram.symm
  cases g;obtain rfl:=eq_of_heq arrived
  exact named_pointer input same B hp reached diagram x edge lo fit

end
end Hierarchy.DescentBundleHistory.Normalized

end OAI
