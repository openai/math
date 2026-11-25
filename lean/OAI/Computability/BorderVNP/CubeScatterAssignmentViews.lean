import OAI.Computability.BorderVNP.CubeScatterAssignment
import OAI.Computability.BorderVNP.CubeISAOwnedVertexModel

/-! # Reading routed choices in the native singleton and packet banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter.Assignment

open Physical Physical.VertexIndex Tally VPVNP.BurstRAM VPVNP.MotifBase
open private vertex_iff from OAI.Computability.BorderVNP.CubeISAOwnedVertexModel

variable {n d blocks b h K s : ℕ} {Team : Type*} {u : Packet n d blocks → Selector n K h}
variable {i : Fin (n+1)} {owner : Fin d → Team}

/-- The owner-side demand lookup reads the unique private bit assigned to that end. -/
def demands (bits : Choices b s u i owner) (p : Packet n d blocks) (e : Ends n) (j : Fin (h*b)) : Bool :=
  lookup bits (.inr (.inl (p,e,j)))

/-- The supply lookup reads the single common bit for a cut edge and the unique
private bit of its tail's team for each other edge. -/
def supplies (bits : Choices b s u i owner) (p : Packet n d blocks) (e : Edge (n+1))
    (j : Fin (payload (onEdge s) (u p).2 e)) : Bool := lookup bits (.inr (.inr ⟨p,e,j⟩))

/-- The actual word on a locally selected side is a complete input to the vertex-table lookup. -/
theorem owned_vertexAt {w : ℕ} (hw : 0 < w) (base : ℕ) (m : Memory w)
    (bits : Choices b s u i owner) (p : Packet n d blocks) (high : Bool) (v : Vertex (n+1))
    (owned : vertexLabel p v i = groupSymbol p i high) :
    let sel := image (selectorPositions (u p)) base m
    let out := image (bodyPositions (u p) i (ownerBit i p.1.2 high) (demands bits p) (supplies bits p))
      (base + selectorWidth n K h) sel
    VertexAt out base (u p) v (demands bits p) (supplies bits p) :=
  image_vertexAt hw base m (u p) i _ v ((vertex_iff ..).mp owned) _ _

/-- The singletons of a diagonal group consume private choices. Every strict row consumes
one shared bit, including when the two groups are assigned to the same executing team. -/
theorem singleton_view (bits : Choices b s u i owner) (k : SingleSlot n d blocks (h*b)) :
    let same := decide (k.1.val.1 i = k.1.val.2 i)
    let bit := lookup bits (.inl k)
    (singlePositions same [bit]).map Position.digit =
      [if same then Digit.privateBit bit else Digit.crossing] ∧
    route (b := b) (s := s) (u := u) i owner (.inl k) =
      if same then Sum.inr (owner (k.1.val.1 i)) else Sum.inl (itemRow i (.inr k)) := by
  by_cases eq : k.1.val.1 i = k.1.val.2 i <;> simp [singlePositions,route,eq,Position.digit]

/-- Two copies of the chosen-axis supply access the very same bit on their two physical sides. -/
theorem crossing_views (bits : Choices b s u i owner) (p : Packet n d blocks) (e : Edge (n+1))
    (cut : e.2 = i) (j : Fin (payload (onEdge s) (u p).2 e)) (high : Bool) :
    let lane : Fin (h*s) := ⟨j.val,j.isLt.trans_le (supplyWidth_le (u p) e s)⟩
    ownedPosition (u p) i (ownerBit i p.1.2 high) (demands bits p) (supplies bits p) (.inr (e,lane)) =
        Position.crossing (supplies bits p e j) ∧
      route (b := b) (s := s) (u := u) i owner (.inr (.inr ⟨p,e,j⟩)) =
        Sum.inl (itemRow (width := h*b) i (.inl p)) := by
  simp only [ownedPosition,route,dite_eq_left j.isLt,cut,ite_true, and_self]

/-- A demand lane occurs on the group symbol of its physical end. -/
theorem demand_view (bits : Choices b s u i owner) (p : Packet n d blocks) (e : Ends n)
    (j : Fin (h*b)) (high : Bool) (owned : vertexLabel p (endVertex e) i = groupSymbol p i high) :
    ownedPosition (u p) i (ownerBit i p.1.2 high) (demands bits p) (supplies bits p) (.inl (e,j)) =
        Position.localBit (demands bits p e j) ∧
      route (b := b) (s := s) (u := u) i owner (.inr (.inl (p,e,j))) =
        Sum.inr (owner (groupSymbol p i high)) := by
  have eq := (vertex_iff ..).mp owned
  simp only [ownedPosition,← show endVertex e = (if e.2 then stop e.1 else start e.1) from rfl,
    eq,ite_true,route,owned,and_self]

/-- An internal supply lane occurs on the group symbol of its tail. -/
theorem internal_view (bits : Choices b s u i owner) (p : Packet n d blocks) (e : Edge (n+1))
    (internal : e.2 ≠ i) (j : Fin (payload (onEdge s) (u p).2 e)) (high : Bool)
    (owned : vertexLabel p e.1 i = groupSymbol p i high) :
    let lane : Fin (h*s) := ⟨j.val,j.isLt.trans_le (supplyWidth_le (u p) e s)⟩
    ownedPosition (u p) i (ownerBit i p.1.2 high) (demands bits p) (supplies bits p) (.inr (e,lane)) =
        Position.localBit (supplies bits p e j) ∧
      route (b := b) (s := s) (u := u) i owner (.inr (.inr ⟨p,e,j⟩)) =
        Sum.inr (owner (groupSymbol p i high)) := by
  have eq := (vertex_iff ..).mp owned
  simp only [ownedPosition,route,dite_eq_left j.isLt,ite_eq_right internal,eq,ite_true,owned,and_self]

end Cube.Scatter.Assignment

end BorderVNP
end Computability
end OAI
