import OAI.Hierarchy.DescentSharedCableNames
import OAI.Hierarchy.DescentParallelBase

namespace OAI
/-! # The fixed group and block shared by actual incident signed parents -/
namespace Hierarchy.DescentParallelBase
open DescentSharedCableNames DescentSixParty
open scoped Classical
noncomputable section
variable {F P J V U : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (order : W.graph.Edge↪ℕ)
local notation "N" => W.graph
local notation "B" => Stage.source A order
local notation "whereAt" => Stage.home A
local notation "H" => Stage.Host J V k
def band (a : (J×V)×DescentColonies.Block k) :=(a.1.1,a.2)

theorem edge_band (e : W.graph.Edge) : band (whereAt (W.graph.src e))=band (whereAt (W.graph.dst e)) := by
  obtain ⟨_,_,atSite⟩:=Finset.mem_map.mp (A.peers e).1
  have group := congrArg (fun pos : J×V => pos.1) atSite
  exact Prod.ext group (A.same e)

variable {E : Type} (C : Blocks (Stage.source A order) E)
theorem parent_band (e : E) (pos : 0<C.count e) : band (C.src e)=band (C.dst e) := by
  let j:Fin (C.count e):=⟨0,pos⟩
  rw [←C.atSource e j,←C.atTarget e j]
  exact edge_band A (((Stage.stream A order).symm (C.order ⟨e,j⟩)).1)

theorem other_band (h : H) (e : Local C h) : band (other C h e)=band h := by
  have source:=parent_band A order C e.val e.property.1
  rcases e.property.2 with arrived|arrived
  · rw [other,ite_eq_left arrived];exact source.symm.trans (congrArg band arrived)
  · unfold other
    split
    · exact congrArg band arrived
    · exact source.trans (congrArg band arrived)

omit [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] in
theorem venue_injective_on_band {X : Type*} (venue : V↪X) {a b : H}
    (same : band a=band b) (at_ : venue a.1.2=venue b.1.2) : a=b := by
  have group : a.1.1 = b.1.1 := congrArg (fun pos : J×DescentColonies.Block k => pos.1) same
  have block : a.2 = b.2 := congrArg (fun pos : J×DescentColonies.Block k => pos.2) same
  exact Prod.ext (Prod.ext group (venue.injective at_)) block

theorem other_venue {X : Type*} (venue : V↪X) (h : H) (e f : Local C h)
    (seen : venue (other C h e).1.2=venue (other C h f).1.2) : other C h e=other C h f :=
  venue_injective_on_band venue ((other_band A order C h e).trans (other_band A order C h f).symm) seen

end
end Hierarchy.DescentParallelBase

end OAI
